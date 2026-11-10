-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_2
-- name    : SunMinCut.Cactus.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:00.246205+00:00
-- url     : https://prove2.me/theorems/417e97e1-1f8a-493e-8af6-19fee8e44516
-- title:
--   Lemma 2.2 — linear search for the cuts of one tree
-- statement:
--   Let $G$ be a connected graph on $n\ge2$ vertices with positive capacities, aggregated so that its $m=s$ records are distinct endpoint pairs, and let $T$ be a spanning tree on $V$ (not necessarily a subgraph of $G$); let $d_0=\min_f d_f$ be the lightest fundamental cut of $T$. There are one admissible program $P$ and one constant $C$ such that, for every such $G$ and $T$ and every encoding of them as input:
--   1. every execution halts within $C(s+n)$ operations and returns an actual cut $S$ (a shore) crossing $T$ at most twice, together with a cactus $(K,\pi)$ with nonempty bags representing exactly the bridges and two-edge bonds of the sampled auxiliary graph. The first $m$ independent tape cells sample the support records with probabilities $p_e=\min(w_e,d_0)/(2d_0)$, and a separate copy of each tree edge is added. The returned cut minimizes original capacity over this cactus family and the fundamental cuts of $T$;
--   2. with probability at least $\tfrac12(1-e^{-1/4})$, $S$ is a lightest cut among all cuts crossing $T$ at most twice;
--   3. every fixed cut $C_0$ crossing $T$ at most twice with $w(C_0)\le d_0$ is represented by the auxiliary cactus with probability at least $\tfrac12(1-e^{-1/4})$;
--   and $\tfrac12(1-e^{-1/4})>1/10$.
--
--   Differences from the source:
--   - encoding: "in O(·) operations the procedure …" (a statement about the paper's procedure) → there exist one admissible program P for the real RAM of footnote 1 and one constant C, chosen before every input, with the stated time bound on every draw tape; reason: the O(·) is unpacked with its constant fixed before the input, and the procedure is the program that realizes it
--   - generalization: a program for the unit-cost real RAM (machine constants unrestricted) → the program must be admissible: rational constants only; reason: a stronger claim; an admissible program is in particular a real-RAM program, so the Lean statement implies the source's
--   - encoding: "with probability at least p" → the (outer) product-uniform measure of the failure set of draw tapes is at most 1 − p; reason: implies the probability statement for the measurable success event and needs no measurability side condition
--   - encoding: input with s aggregated endpoint pairs and bound in s → Aggregated G (no loops, no repeated pair), so m = s, and the bound written with m; reason: the procedure takes the aggregated graph of §2 as input
--   - encoding: the auxiliary cactus of the sampled graph and minimization over its cuts and the lightest fundamental cut → the first m tape cells sample auxGraph; the output cactus has surjective π and repCuts exactly the bipartitions of its small bonds; the returned candidate has capacity at most d0 and every represented cut; reason: p. 7 identifies the contracted cactus by precisely this cut family; this pins the constructed object and candidate minimization, with no graph oracle
--   - encoding: the arithmetic, logarithm and power operations of footnote 1 → division by zero is zero, log uses log(abs x), and power returns zero on negative bases instead of using the cosine continuation of Real.rpow; reason: explicit totalization at exceptional inputs using constant-cost guards; the paper’s uses of real powers have nonnegative bases and no trigonometric operation is introduced
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.2, p. 7

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Machine
import Definitions.Def_SunMinCut_Cactus_Processes

open MeasureTheory

namespace SunMinCut.Cactus

/-- **Lemma 2.2 (Linear search for the cuts of one tree)**, Sun 2026, doi:10.5281/zenodo.23915020,
p. 7. There are one program `P` and one constant `C` such that, on every aggregated connected
graph `G` with positive capacities (`m = s` records) and every spanning tree `T` on its vertices
(not necessarily a subgraph of `G`), every execution halts within `C (s + n)` operations and
returns an actual cut `S` crossing `T` at most twice together with an auxiliary cactus `(K, π)`;
`S` is a lightest cut crossing `T` at most twice with probability at least `½(1 − e^{−1/4})`,
which exceeds `1/10`; and every fixed cut `C₀` crossing `T` at most twice with `w(C₀) ≤ d₀` is
represented by the auxiliary cactus with at least that probability. The first `m` tape cells
sample the support records by (2). On every tape, the output cactus represents exactly the
bridges and two-edge bonds of that auxiliary graph, and the returned cut minimizes the original
capacity over its represented cuts and the fundamental cuts of `T`. -/
theorem lemma_2_2 :
    1 / 10 < (1 - Real.exp (-1 / 4)) / 2 ∧
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (n m : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G → Aggregated G →
      ∀ T : SimpleGraph (Fin n), T.IsTree →
      ∀ lG lT : List ℝ, GraphCode G lG → EdgeListCode T lT →
        HaltsWithin P (lG ++ lT) (C * ((m : ℝ) + n)) ∧
        (∀ ω : Tape, ∃ (S : Finset (Fin n)) (q e : ℕ) (K : MGraph q e) (π : Fin n → Fin q),
          CutCactusOut S K π (outputAt P (lG ++ lT) (C * ((m : ℝ) + n)) ω) ∧
          K.IsCactus ∧ Function.Surjective π ∧
          repCuts K π = bip '' {S' | IsSmallBond (auxGraph G T (fun e => ω e.val)) S'} ∧
          Nontriv S ∧ crossT T S ≤ 2 ∧
          (bip S ∈ repCuts K π ∨ crossT T S = 1) ∧ cutw G S ≤ d0 G T ∧
          ∀ S', bip S' ∈ repCuts K π → cutw G S ≤ cutw G S') ∧
        tapeMeasure {ω | ¬ ∃ (S : Finset (Fin n)) (q e : ℕ) (K : MGraph q e) (π : Fin n → Fin q),
          CutCactusOut S K π (outputAt P (lG ++ lT) (C * ((m : ℝ) + n)) ω) ∧
          ∀ S' : Finset (Fin n), Nontriv S' → crossT T S' ≤ 2 → cutw G S ≤ cutw G S'} ≤
          ENNReal.ofReal (1 - (1 - Real.exp (-1 / 4)) / 2) ∧
        ∀ S₀ : Finset (Fin n), Nontriv S₀ → crossT T S₀ ≤ 2 → cutw G S₀ ≤ d0 G T →
          tapeMeasure {ω | ¬ ∃ (S : Finset (Fin n)) (q e : ℕ) (K : MGraph q e)
            (π : Fin n → Fin q),
            CutCactusOut S K π (outputAt P (lG ++ lT) (C * ((m : ℝ) + n)) ω) ∧
            bip S₀ ∈ repCuts K π} ≤
          ENNReal.ofReal (1 - (1 - Real.exp (-1 / 4)) / 2) := by sorry

end SunMinCut.Cactus
