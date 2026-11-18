-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_regression_programs
-- name    : PrivateAgnosticHalfspace.Gaussian.ordered_regression_programs
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:30.282313+00:00
-- url     : https://prove2.me/theorems/cbaf6d88-76bf-422d-b97a-f06b90f96c74
-- title:
--   Finite programs realizing the ordered regression learner
-- statement:
--   Let $d,p$ be the input dimension and Hermite cutoff degree, let $D_p=\binom{d+p}{p}$, and use the clipped Hermite features, unit coefficient ball and midpoint threshold grid of Algorithm 1. There are two fixed arithmetic programs for optimization and learning. For every probability-valued optimizer realizing the canonical ordered Gaussian regression law, these programs implement its optimization output and Algorithm 1's learning law on every deterministic dataset.
--
--   For $p\ge1$, $n\ge2$ and $\varepsilon,\delta\in(0,1/2]$, the optimizer's charged cost is at most
--
--   $$100000(npD_p+n^2D_p).$$
--
--   For positive integers $k,M,m$, degree $p\ge1$, and training block size $n_0$ satisfying $D_p\le n_0$, $m\le kn_0$, $p\le D_p$ and $M\le p$, the learner uses $N=kn_0+m$ examples and has charged cost at most
--
--   $$100000(NpD_p+kn_0^2D_p+kMmD_p)\le 3\cdot100000N^3.$$
--
--   The second claim holds for $\varepsilon,\delta\in(0,1/2]$ and arbitrary real accuracy and confidence inputs. Each execution halts with bounded fuel, returns a valid coefficient and threshold output, and has exactly the specified law, including all Gaussian training and exponential validation coins. The programs are chosen before dimensions, datasets, public parameters and the optimizer family. This is the operational component of Theorem 2.1; it imposes no population-distribution assumption.
-- source:
--   Racca, Sanyal and Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, held STOC 2027 submission #1006, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1006.pdf, Algorithm 1, §2.1 equation (4), Appendix B Lemma B.4, and §2.2 arithmetic account. Derived finite Gaussian regression implementation; accelerated recurrence: Ghadimi and Lan, https://arxiv.org/abs/1310.3787v1, p.22 equation (3.36).

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem PrivateAgnosticHalfspace.Gaussian.ordered_regression_programs :
    ∃ optimizerCode learnerCode : LearnerProgram,
    ∀ O : Optimizer, RealizesOrderedRegression O →
      (∀ d p n : ℕ, 1 ≤ p → 2 ≤ n → ∀ ε δ : ℝ,
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        ∀ S : Fin n → Example d, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ (100000 : ℝ)*((n : ℝ)*p*featureDimension d p+n^2*featureDimension d p) ∧
          Implements optimizerCode fuel cost d p 1 (optimizerInput d p n ε δ S)
            ((O d p n ε δ S : Measure (UnitBall d p)).map (fun v => (v,(0 : Fin 1))))) ∧
      (∀ d p k M n₀ m : ℕ, 1 ≤ p → 0 < k → 0 < M → 0 < m →
        featureDimension d p ≤ n₀ → m ≤ k*n₀ → p ≤ featureDimension d p → M ≤ p →
        ∀ ε δ α β : ℝ, 0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        ∀ S : Fin (k*n₀+m) → Example d, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ (100000 : ℝ)*(((k*n₀+m : ℕ) : ℝ)*p*featureDimension d p+
            (k : ℝ)*n₀^2*featureDimension d p+(k : ℝ)*M*m*featureDimension d p) ∧
          (cost : ℝ) ≤ 3*(100000 : ℝ)*((k*n₀+m : ℕ) : ℝ)^3 ∧
          Implements learnerCode fuel cost d p M (learnerInput d p k M n₀ m ε δ α β S)
            (algorithmLaw O d p k M n₀ m ε δ S)) := by sorry
