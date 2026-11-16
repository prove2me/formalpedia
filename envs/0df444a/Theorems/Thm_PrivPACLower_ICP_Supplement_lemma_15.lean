-- Prove2me | Theorems.Thm_PrivPACLower_ICP_Supplement_lemma_15
-- name    : PrivPACLower.ICP.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:27.946728+00:00
-- url     : https://prove2.me/theorems/0e98f4d3-ec06-493e-99ab-7890d9df93e5
-- title:
--   Lemma 15 (used in the proof of Theorem 9) — private accuracy and confidence amplification
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $G\subseteq\{0,1\}^Y$ with $Y$ nonempty, $0<\varepsilon\le1$ and $0\le\delta<1$. If $G$ has an $(\varepsilon,\delta)$-DP, $(1/4,1/4)$-PAC learner using $m\ge1$ examples, then for every $0<\eta,\gamma\le1/3$ it has an $(\varepsilon,\delta)$-DP, $(\eta,\gamma)$-PAC learner using at most
--   $$C\,\frac{m}{\eta}\log^2\frac2\eta\,\log\frac2\gamma$$
--   examples. Both learners may be improper.
--
--   Privacy is unchanged; only the sample size grows. This lets component learners be combined with errors summing to the target accuracy.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases and probability-measure outputs on the product sigma-algebra of hypotheses; reason: the published interface of the base mission; replacement adjacency, improper outputs and the joint sample-and-learner experiment are kept
--   - reading: a distribution over an arbitrary domain X x {0,1}, with no sigma-algebra specified; privacy for every event → probability mass functions on X x {0,1}; privacy for product-measurable events of the hypothesis space (the base mission's published convention); reason: on a bare set the only sigma-algebra available is the power set, and below a real-valued measurable cardinal every probability measure on the power set is atomic, i.e. a PMF; the same convention is used in the published goal
--   - encoding: a learner "using at most" the displayed number of examples → some n with n <= the displayed bound and an (epsilon, delta)-DP, (eta, gamma)-PAC learner on n examples; reason: literal transcription
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 30, Lemma 15 (proof pp. 46–47). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
import Definitions.Def_PrivPACLower_ICP_Packing
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP.Supplement

open PrivateUniformGen.Characterization PrivPACLower.ICP


theorem lemma_15 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Y : Type*} (_ : Nonempty Y) (G : Set (Y → Bool)) (ε δ : ℝ),
        0 < ε → ε ≤ 1 → 0 ≤ δ → δ < 1 →
        ∀ m : ℕ, 1 ≤ m →
          (∃ M : Learner Y m, IsDP M ε δ ∧ IsPACLearner G M (1/4) (1/4)) →
          ∀ η γ : ℝ, 0 < η → η ≤ 1/3 → 0 < γ → γ ≤ 1/3 →
            ∃ n : ℕ, (n : ℝ) ≤ C * (m / η) * Real.log (2 / η) ^ 2 * Real.log (2 / γ) ∧
              ∃ M : Learner Y n, IsDP M ε δ ∧ IsPACLearner G M η γ := by sorry

end PrivPACLower.ICP.Supplement
