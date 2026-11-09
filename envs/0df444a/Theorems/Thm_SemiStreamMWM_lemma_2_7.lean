-- Prove2me | Theorems.Thm_SemiStreamMWM_lemma_2_7
-- name    : SemiStreamMWM.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:30:34.213104+00:00
-- url     : https://prove2.me/theorems/cf4fff23-dfe7-49fb-a63c-be5e68e630e1
-- title:
--   Lemma 2.7 — Algorithm 2.2 returns a fractional $(1-\varepsilon)$-MWM in $O(\log W/\varepsilon^2)$ iterations (corrected: $G$ has an edge)
-- statement:
--   Let $G$ have integer weights in $[1,W]$, $W\ge8$ a power of two; let $c\ge1$ be the oracle constant, $C\ge\max\{64,8c^2\}$, $0<\varepsilon\le1$, and $L$ any number with $\mu_w(G)/4\le L\le\mu_w(G)$. Run Algorithm 2.2: start at $x=0$, $t=1/(32\log W)$, and while $t\ge\varepsilon/(C\log W)$ replace $x$ by the output of Algorithm 2.1 on $(x,t,L)$ and halve $t$. Then, whatever admissible answers the oracles give:
--
--   1. if $G$ has at least one edge, the total number of iterations is at most $A\log W/\varepsilon^2$, where $A$ depends only on $c$ and $C$;
--   2. the returned $x$ is a fractional $(1-\varepsilon)$-MWM: $x\in\mathcal P_G$ and $w^\top x\ge(1-\varepsilon)\mu_w(G)$.
--
--   This is the iteration bound of the framework; the streaming algorithm of §4 implements each iteration in $O(1)$ passes.
--
--   Differences from the source:
--   - correction: the iteration bound for every graph → the iteration bound for graphs with an edge (`G.edgeSet.Nonempty →`); reason: for a graph with no edge L = 0 and Algorithm 2.1 never returns (see Lemma 2.5), so Algorithm 2.2 never returns
--   - reading: Algorithm 2.2 returns … in O(log W/ε²) iterations → every prefix of every run, for all admissible oracle answers, has at most A log W/ε² iterations, and every complete run returns a fractional (1 − ε)-MWM; reason: the oracles are specified only by Definitions 2.3–2.4 (paper.md decision 9)
--   - encoding: O(log W/ε²) → A · log W / ε² with ∃ A after c and C and before the instance; reason: c and C are the fixed constants of the algorithm
--   - encoding: the standing assumptions (integer weights in [1, W], W ≥ 8 a power of two) → hypothesis `Standing G w W`; reason: trap 19: the section's assumptions are binders; no instance changes
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), Lemma 2.7, p.12; Algorithm 2.2, p.12

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph
import Definitions.Def_SemiStreamMWM_Potential
import Definitions.Def_SemiStreamMWM_Algorithms

open Classical

namespace SemiStreamMWM

/-- J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), Lemma 2.7, p.12, for
Algorithm 2.2 (p.12) with Algorithm 2.1 and the oracles of Definitions 2.3, 2.4 (pp.10–11).

"Algorithm 2.2 returns a fractional (1 − ε)-MWM in O(log W/ε²) iterations."

**Formalization Note.** Algorithm 2.2 fixes `C ≥ max{64, 8c²}` with `c` the oracle constant
(p.12); it requires `0 < ε ≤ 1` and obtains `L` with `µ_w(G)/4 ≤ L ≤ µ_w(G)`, which is any such `L`.
The `O`-constant `A` depends on `c` and `C` only. The iteration count is the sum, over the phases
entered so far, of the iterations of Algorithm 2.1 (each list of a phase counts its iterations,
including the returning one), and it is bounded for **every** prefix of every run, whatever
admissible answers the oracles give; the output clause holds for every complete run. A fractional
`(1 − ε)`-MWM is a point of `P_G` with `w^⊤x ≥ (1 − ε)µ_w(G)`. Correction: for a graph with no edge
Algorithm 2.1 never returns (see Lemma 2.5), so the iteration bound is stated for graphs with an
edge. -/
theorem lemma_2_7 : ∀ c : ℝ, 1 ≤ c → ∀ C : ℝ, max 64 (8 * c ^ 2) ≤ C → ∃ A : ℝ,
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℕ) (W : ℕ) (ε L : ℝ),
      Standing G w W → 0 < ε → ε ≤ 1 → (mwm G w : ℝ) / 4 ≤ L → L ≤ mwm G w →
      (G.edgeSet.Nonempty → ∀ (N J : ℕ) (tr : ℕ → List (G.edgeSet → ℝ)),
          Alg22Prefix G w W c C ε L N J tr →
          ∑ j ∈ Finset.range J, ((tr j).length : ℝ) ≤ A * logW W / ε ^ 2) ∧
      (∀ (N : ℕ) (tr : ℕ → List (G.edgeSet → ℝ)) (x : G.edgeSet → ℝ),
          Alg22Output G w W c C ε L N tr x →
          x ∈ matchingPolytope G ∧ (1 - ε) * (mwm G w : ℝ) ≤ wdot G (weightVec G w) x) := by sorry

end SemiStreamMWM
