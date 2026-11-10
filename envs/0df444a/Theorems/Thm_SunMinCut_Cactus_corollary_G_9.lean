-- Prove2me | Theorems.Thm_SunMinCut_Cactus_corollary_G_9
-- name    : SunMinCut.Cactus.corollary_G_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:20.097185+00:00
-- url     : https://prove2.me/theorems/cb14cfab-db87-48a5-a74a-8319a0f8619d
-- title:
--   Corollary G.9 — searching and filtering the cuts of a cactus in O(s + n)
-- statement:
--   Let $G$ be a connected aggregated graph ($m=s$ records) on $n\ge2$ vertices with positive capacities, $K$ a connected loopless cactus on $q\ge2$ vertices with a surjection $\pi:V\to V(K)$, and $r$ the root; the input is $G$, $(K,\pi)$ and $r$.
--   1. The lightest original cut represented by $K$ can be found in $O(s+n)$ deterministic work: one program and one constant $C$ such that every execution halts within $C(s+n)$ operations and outputs a represented shore $S$ excluding $r$ with $w(S)\le w(S')$ for every represented $S'$.
--   2. If $\ell\ge0$ lower-bounds every represented cut, exactly its value-$\ell$ cuts can be filtered in the same work, and the unique smallest such represented shore containing each original vertex, or both endpoints of each original edge, can be found within that bound, or reported absent: one program and one constant $C$ such that, given also $\ell$, every execution halts within $C(s+n)$ operations and outputs a compact description (a ring of cactus vertices with explicit pairs, suffixes and boundary lists) whose denoted shores are exactly the represented root-avoiding shores of weight $\ell$, followed, for each vertex $v$ and each record $e$, by an interval of that ring denoting the smallest represented root-avoiding value-$\ell$ shore containing $v$ (resp. both endpoints of $e$), or the absence code exactly when there is none.
--
--   Differences from the source:
--   - encoding: "in O(·) operations the procedure …" (a statement about the paper's procedure) → there exist one admissible program P for the real RAM of footnote 1 and one constant C, chosen before every input, with the stated time bound on every draw tape; reason: the O(·) is unpacked with its constant fixed before the input, and the procedure is the program that realizes it
--   - generalization: a program for the unit-cost real RAM (machine constants unrestricted) → the program must be admissible: rational constants only; reason: a stronger claim; an admissible program is in particular a real-RAM program, so the Lean statement implies the source's
--   - encoding: input with s aggregated endpoint pairs and bound in s → Aggregated G (no loops, no repeated pair), so m = s, and the bound written with m; reason: the procedure takes the aggregated graph of §2 as input
--   - encoding: deterministic work (Appendix B.1 or Appendix G) → Deterministic P forbids uniform-draw instructions, with the guarantee on every tape; reason: the run is independent of the tape; this states determinism directly
--   - encoding: "filtered" and "found" (output form unspecified) → the description format of App. G.1 (pairs, suffixes, boundary lists over a ring) and ring intervals for the smallest shores; reason: these are the compact forms of Theorem G.6 and Lemma G.7, which the corollary applies
--   - encoding: the arithmetic, logarithm and power operations of footnote 1 → division by zero is zero, log uses log(abs x), and power returns zero on negative bases instead of using the cosine continuation of Real.rpow; reason: explicit totalization at exceptional inputs using constant-cost guards; the paper’s uses of real powers have nonnegative bases and no trigonometric operation is introduced
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Corollary G.9, p. 48

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Machine
import Definitions.Def_SunMinCut_Cactus_Intervals

namespace SunMinCut.Cactus

/-- **Corollary G.9 (Searching and filtering the cuts of a cactus)**, Sun 2026,
doi:10.5281/zenodo.23915020, p. 48. Inputs: an aggregated connected graph `G` with positive
capacities (`m = s` records), a connected loopless cactus `K` on `q ≥ 2` vertices with a
surjection `π : V(G) → V(K)`, and the root `r`. (1) The lightest original cut represented by `K`
can be found in `O(s + n)` deterministic work. (2) If `ℓ ≥ 0` lower-bounds every represented cut,
exactly its value-`ℓ` (root-avoiding) cuts can be filtered in the same work, as a compact
description by pairs, suffixes and boundary lists over a ring of positions; and the unique
smallest such represented shore containing each original vertex, or both endpoints of each
original record, is found within that bound (as an interval of that ring), or reported absent. -/
theorem corollary_G_9 :
    (∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ,
      ∀ (n m q e : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G → Aggregated G →
      ∀ K : MGraph q e, K.IsCactus → 2 ≤ q → ∀ π : Fin n → Fin q, Function.Surjective π →
      ∀ r : Fin n, ∀ lG lK : List ℝ, GraphCode G lG → CactusCode K π lK →
        HaltsWithin P (lG ++ lK ++ [((r : ℕ) : ℝ)]) (C * ((m : ℝ) + n)) ∧
        ∀ ω : Tape, ∃ S : Finset (Fin n),
          outputAt P (lG ++ lK ++ [((r : ℕ) : ℝ)]) (C * ((m : ℝ) + n)) ω = shoreList S ∧
          bip S ∈ repCuts K π ∧ r ∉ S ∧ ∀ S', bip S' ∈ repCuts K π → cutw G S ≤ cutw G S') ∧
    (∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ,
      ∀ (n m q e : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G → Aggregated G →
      ∀ K : MGraph q e, K.IsCactus → 2 ≤ q → ∀ π : Fin n → Fin q, Function.Surjective π →
      ∀ r : Fin n, ∀ ℓ : ℝ, 0 ≤ ℓ → (∀ S, bip S ∈ repCuts K π → ℓ ≤ cutw G S) →
      ∀ lG lK : List ℝ, GraphCode G lG → CactusCode K π lK →
        HaltsWithin P (lG ++ lK ++ [((r : ℕ) : ℝ), ℓ]) (C * ((m : ℝ) + n)) ∧
        ∀ ω : Tape, ∃ (D : IntervalDesc) (lv : Fin n → Option (ℕ × ℕ))
            (le : Fin m → Option (ℕ × ℕ)),
          outputAt P (lG ++ lK ++ [((r : ℕ) : ℝ), ℓ]) (C * ((m : ℝ) + n)) ω =
            D.code ++ (List.ofFn fun v => optIntervalCode (lv v)).flatten ++
              (List.ofFn fun x => optIntervalCode (le x)).flatten ∧
          D.shores π = {S | bip S ∈ repCuts K π ∧ r ∉ S ∧ cutw G S = ℓ} ∧
          let 𝓕 : Set (Finset (Fin n)) := {S | bip S ∈ repCuts K π ∧ cutw G S = ℓ}
          let ok : Finset (Fin n) → Option (ℕ × ℕ) → Prop := fun Z o =>
            (o = none ↔ feasible 𝓕 r Z = ∅) ∧
            ∀ ab, o = some ab → 1 ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < D.occ.length ∧
              IsLeast' (feasible 𝓕 r Z) (ringShore D.occ π ab.1 ab.2)
          (∀ v, ok {v} (lv v)) ∧ ∀ x, ok (recordEnds G x) (le x)) := by sorry

end SunMinCut.Cactus
