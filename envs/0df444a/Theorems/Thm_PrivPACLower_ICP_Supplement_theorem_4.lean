-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_4
-- name    : PrivPACLower.ICP.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:15.630789+00:00
-- url     : https://prove2.me/theorems/296abf8b-f7d0-4916-be92-fcb65797d4b6
-- title:
--   Theorem 4 — empirical threshold lower bound log* N ≤ m + log* m + C
-- statement:
--   There are universal constants $c,C>0$ such that the following holds for all integers $N\ge1$ and $m\ge2$. Let $A$ be a $(0.1,\delta)$-DP algorithm that maps databases of size $m$ over $[N]\times\{0,1\}$ to hypotheses on $[N]$, with $\delta\le c/m$, and suppose that
--   $$\Pr\bigl[\mathrm{err}_S(A(S))\le 1/16\bigr]\ge 15/16$$
--   for every database $S$ of size $m$ realizable by $\mathrm{Thr}_N$. Then
--   $$\log^* N\le m+\log^* m+C.$$
--
--   In particular such an algorithm needs $\Omega(\log^* N)$ examples; unlike the earlier bound of Alon et al., it requires only $\delta\le c/m$.
--
--   **Formalization Note** $A$ is an arbitrary randomized map from databases to hypotheses (improper). The empirical error is the fraction of misclassified examples, valued in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - encoding: every distribution over the finite labelled domain and every output event → PMFs over the labelled domain and product-measurable output events; reason: on a finite domain every distribution is a PMF and every set of hypotheses is measurable, so no instance changes
--   - encoding: Pr[err_S(A(S)) <= 1/16] >= 15/16 → ofReal(15/16) <= (A S){h | empiricalError S h <= ofReal(1/16)}; reason: literal transcription; the event is measurable on the finite hypothesis space
--   - encoding: the grid [N] = {1, ..., N} (and [N]^d, [N]^2) → Fin N with x standing for x + 1 (real coordinates (x : R) + 1 in halfspaces and halfplanes); reason: a bijective relabelling of the finite domain; no instance changes
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 18, Theorem 4 (restated p. 44 with proof pp. 44–46). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Supplement_Basics
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem theorem_4 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ N m : ℕ, 1 ≤ N → 2 ≤ m → ∀ δ : ℝ, δ ≤ c / m →
        ∀ A : Learner (Fin N) m, IsDP A (1/10) δ →
          (∀ S : Fin m → Fin N × Bool, RealizableDB (Thr N) S →
            ENNReal.ofReal (15/16) ≤
              (A S : Measure (Fin N → Bool)) {h | empiricalError S h ≤ ENNReal.ofReal (1/16)}) →
          (logStar (N : ℝ) : ℝ) ≤ m + logStar (m : ℝ) + C := by sorry

end PrivPACLower.ICP.Supplement
