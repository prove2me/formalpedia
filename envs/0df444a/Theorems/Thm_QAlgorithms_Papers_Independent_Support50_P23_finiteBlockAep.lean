-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_finiteBlockAep
-- name    : QAlgorithms.Papers.Independent.Support50.P23.finiteBlockAep
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:02:29.384423+00:00
-- url     : https://prove2.me/theorems/d46a8100-25ee-48ee-b44c-0f8d95aacf67
-- title:
--   Dimension-independent finite-block quantum AEP
-- statement:
--   Let $\rho_{AB}$ be a normalized finite-dimensional state, let $n\ge1$ be an integer, and put $\eta=\Upsilon(A|B)_{\rho|\rho_B}$, where $\rho_B=\operatorname{tr}_A\rho_{AB}$. For $0<\varepsilon<1$ and $n\ge\frac85\log_2(2/\varepsilon^2)$, set $\delta(\varepsilon,\eta)=4\log_2\eta\sqrt{\log_2(2/\varepsilon^2)}$. Then
--   $$
--   \frac1n H_{\min}^{\varepsilon}(A^n|B^n)_{\rho^{\otimes n}}
--   \ge H(A|B)_\rho-\frac{\delta(\varepsilon,\eta)}{\sqrt n}.
--   $$
--   For $\varepsilon\ge1$, the smooth min entropy is $+\infty$. The printed unrestricted real square-root formula requires this domain repair; no explicit small-$n$ error is supplied. The quantitative bound contains no dimension factor for $B$.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 6, Theorem 9: dimension-independent finite-block AEP, (30)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

noncomputable section

open Filter

open scoped ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P23

attribute [local instance] Classical.propDecidable

-- Exact accepted bodies. Other similarly named catalogue entries use different
-- smoothing, conditioning order, logarithm base, or channel-level objects.

open QAlgorithms.Papers.Independent.Gap20.P03 (fixedMin)

open QAlgorithms.Papers.Independent.Dependency50.P36 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P69 (matrixPower)

variable {A B C D I : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq I]

/-- Theorem 9, PDF p.6, (30). Domain correction: the displayed real square root is
used for 0<epsilon<1 above the 8/5 threshold; epsilon>=1 is the trivial +infinity
branch. The printed formula is not real for epsilon>sqrt(2). No small-n error is invented. -/
theorem finiteBlockAep [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((epsilon < 1 ∧ (8 / 5 : ℝ) * Real.logb 2 (2 / epsilon ^ 2) ≤ (n : ℝ)) →
      ((conditionalEntropyBitsAB rho -
        aepBlockError epsilon (entropyConvergenceParameter rho (traceLeft rho)) / Real.sqrt (n : ℝ) : ℝ) : EReal) ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal) * sineSmoothMin (jointPower rho n) epsilon) ∧
    (1 ≤ epsilon → sineSmoothMin (jointPower rho n) epsilon = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
