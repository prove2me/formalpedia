-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P23_alphaOneLimit
-- name    : QAlgorithms.Papers.Independent.Support50.P23.alphaOneLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:06:36.873254+00:00
-- url     : https://prove2.me/theorems/d1819097-6e02-4e97-8a2f-3cb763a47e2e
-- title:
--   Order-one limit at a fixed reference
-- statement:
--   Let $\rho_{AB}$ and $\sigma_B$ be normalized finite-dimensional states. With the source's singular-reference regularization,
--   $$
--   \lim_{\substack{\alpha\to1\\\alpha>0,\ \alpha\ne1}}H_\alpha(A|B)_{\rho|\sigma}
--   =H(A|B)_{\rho|\sigma}=H_1(A|B)_{\rho|\sigma}.
--   $$
--   The convergence is in the extended real line, including $-\infty$ on support failure. This identifies the order-one member without optimizing the reference.
-- source:
--   A Fully Quantum Asymptotic Equipartition Property, arXiv:0811.1221v3, PDF p. 4, Section II, unnumbered: order-one limit

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

/-- Section II, PDF p.4: genuine order-one extended-real convergence, including
singular references, together with the identity at one. -/
theorem alphaOneLimit [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    Tendsto (finiteAlpha rho sigma)
      (nhdsWithin 1 {t : ℝ | 0 < t ∧ t ≠ 1}) (nhds (fixedVonNeumann rho sigma)) ∧
      alphaEntropy rho sigma 1 = fixedVonNeumann rho sigma := by sorry

end QAlgorithms.Papers.Independent.Support50.P23

end
