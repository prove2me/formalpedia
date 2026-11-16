-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_theorem_11
-- name    : PrivPACLower.ICP.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:19:04.385549+00:00
-- url     : https://prove2.me/theorems/276f3ce8-c085-4d33-88e0-e21b2bc3385d
-- title:
--   Theorem 11 — proper private learner for unions of intervals
-- statement:
--   There is a universal constant $C\ge2$ such that for all integers $k\ge1$, $N\ge2k$ and all $0<\varepsilon\le1$, $0<\alpha,\beta,\delta\le1/4$, the class $I_{N,k}$ has a proper, realizable, $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner using at most
--   $$\frac{Ck}{\alpha\varepsilon}\Bigl[\ell_N\log^2\Bigl(\frac{Ck\ell_N}{\alpha\beta\delta}\Bigr)+\log\Bigl(\frac C\beta\Bigr)\log^{5/2}\Bigl(\frac{Ck}{\alpha}\Bigr)\Bigr]\tag{22}$$
--   examples, where $\ell_N=\log^*(\max\{2,N\})$.
--
--   The learner is private on every database, including non-realizable ones, and always outputs a union of at most $k$ intervals. Its dependence on $N$ is $\widetilde O(k\log^*N)$, close to the lower bound of Theorem 5.
--
--   **Formalization Note** "Proper" means that for every input database the output lies in $I_{N,k}$ almost surely; "realizable" means the PAC guarantee is required for realizable distributions. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - encoding: every distribution over the finite labelled domain and every output event → PMFs over the labelled domain and product-measurable output events; reason: on a finite domain every distribution is a PMF and every set of hypotheses is measurable, so no instance changes
--   - encoding: a learner "with sample complexity at most" (22) → some n <= (22) and a learner on n examples that is proper, (epsilon, delta)-DP and (alpha, beta)-PAC; reason: literal transcription
--   - encoding: the grid [N] = {1, ..., N} (and [N]^d, [N]^2) → Fin N with x standing for x + 1 (real coordinates (x : R) + 1 in halfspaces and halfplanes); reason: a bijective relabelling of the finite domain; no instance changes
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 48, Theorem 11 (proof pp. 48–49). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
import Definitions.Def_PrivPACLower_ICP_Supplement_Classes
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem theorem_11 :
    ∃ C : ℝ, 2 ≤ C ∧
      ∀ N k : ℕ, 1 ≤ k → 2 * k ≤ N →
        ∀ ε α β δ : ℝ, 0 < ε → ε ≤ 1 → 0 < α → α ≤ 1/4 → 0 < β → β ≤ 1/4 →
          0 < δ → δ ≤ 1/4 →
          ∃ n : ℕ,
            (n : ℝ) ≤ C * k / (α * ε) *
              (ellStar N * Real.log (C * k * ellStar N / (α * β * δ)) ^ 2 +
                Real.log (C / β) * Real.log (C * k / α) ^ (5/2 : ℝ)) ∧
            ∃ L : Learner (Fin N) n, ProperLearner (Intervals N k) L ∧ IsDP L ε δ ∧
              IsPACLearner (Intervals N k) L α β := by sorry

end PrivPACLower.ICP.Supplement
