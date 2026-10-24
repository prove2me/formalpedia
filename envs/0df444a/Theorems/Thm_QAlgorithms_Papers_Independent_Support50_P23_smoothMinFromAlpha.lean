-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_smoothMinFromAlpha
-- name    : QAlgorithms.Papers.Independent.Support50.P23.smoothMinFromAlpha
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:00:27.986381+00:00
-- url     : https://prove2.me/theorems/53b973f9-0e12-4973-bda6-7931b6da6225
-- title:
--   Smooth min entropy from fixed-reference alpha entropy
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states. For every $\varepsilon>0$ and $1<\alpha\le2$,
--   $$
--   H_{\min}^{\varepsilon}(A|B)_{\rho|\sigma}\ge H_\alpha(A|B)_{\rho|\sigma}-\frac{\log_2(2/\varepsilon^2)}{\alpha-1}.
--   $$
--   Smoothing uses the closed subnormalized root-fidelity ball and holds the reference fixed. No support hypothesis is imposed: support failure can give $H_\alpha=-\infty$, and $\varepsilon\ge1$ gives smooth min entropy $+\infty$. This is the bridge from Petz entropy to one-shot smooth min entropy.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Theorem 7: smooth min entropy from alpha entropy, (22)

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

/-- Theorem 7, PDF p.4, (22). No support restriction is added. All epsilon>0 are
retained; epsilon>=1 makes the left hand side +infinity. -/
theorem smoothMinFromAlpha [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) (halpha : 1 < alpha) (halpha2 : alpha ≤ 2) :
    finiteAlpha rho sigma alpha -
      ((Real.logb 2 (2 / epsilon ^ 2) / (alpha - 1) : ℝ) : EReal) ≤
        sineSmoothFixedMin rho sigma epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
