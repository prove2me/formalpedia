-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_learner_program
-- name    : PrivateAgnosticHalfspace.Gaussian.ordered_learner_program
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:36.191205+00:00
-- url     : https://prove2.me/theorems/6b5e3e5d-d63a-4fc5-8acd-4961e94c6e07
-- title:
--   Learner program: exact law, termination and operation bounds
-- statement:
--   Write $D_p=\binom{d+p}{p}$ for the clipped Hermite feature dimension. There exists one fixed arithmetic learning program. Let $p,k,M,m$ be positive natural numbers and $n_0$ a training block size satisfying $D_p\le n_0$, $m\le kn_0$, $p\le D_p$ and $M\le p$. For every optimizer realizing the ordered finite Gaussian regression law, $\varepsilon,\delta\in(0,1/2]$, arbitrary real accuracy and confidence inputs, and every deterministic dataset of size $N=kn_0+m$, the program halts with a valid coefficient and threshold output and has exactly Algorithm 1's output law. Its charged cost obeys
--
--   $$\mathrm{cost}\le100000(NpD_p+kn_0^2D_p+kMmD_p)\le3\cdot100000N^3.$$
--
--   The output law includes all independent Gaussian training records and the exponential validation draw. The program is chosen before all dimensions, parameters, datasets and the optimizer family. This is the learning-program component of the operational theorem and requires no Gaussian-distribution assumption on the deterministic input dataset.
-- source:
--   Racca, Sanyal and Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, held STOC 2027 submission #1006, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1006.pdf, Algorithm 1, §2.1 equation (4), Appendix B Lemma B.4, and §2.2 arithmetic account. Derived finite Gaussian regression implementation; accelerated recurrence: Ghadimi and Lan, https://arxiv.org/abs/1310.3787v1, p.22 equation (3.36).

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem PrivateAgnosticHalfspace.Gaussian.ordered_learner_program :
    ∃ learnerCode : LearnerProgram,
    ∀ O : Optimizer, RealizesOrderedRegression O →
      (∀ d p k M n₀ m : ℕ, 1 ≤ p → 0 < k → 0 < M → 0 < m →
        featureDimension d p ≤ n₀ → m ≤ k*n₀ → p ≤ featureDimension d p → M ≤ p →
        ∀ ε δ α β : ℝ, 0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        ∀ S : Fin (k*n₀+m) → Example d, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ (100000 : ℝ)*(((k*n₀+m : ℕ) : ℝ)*p*featureDimension d p+
            (k : ℝ)*n₀^2*featureDimension d p+(k : ℝ)*M*m*featureDimension d p) ∧
          (cost : ℝ) ≤ 3*(100000 : ℝ)*((k*n₀+m : ℕ) : ℝ)^3 ∧
          Implements learnerCode fuel cost d p M (learnerInput d p k M n₀ m ε δ α β S)
            (algorithmLaw O d p k M n₀ m ε δ S)) := by sorry
