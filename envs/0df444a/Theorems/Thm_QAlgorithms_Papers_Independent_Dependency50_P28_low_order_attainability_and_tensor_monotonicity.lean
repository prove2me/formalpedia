-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_low_order_attainability_and_tensor_monotonicity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.low_order_attainability_and_tensor_monotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:14:20.682764+00:00
-- url     : https://prove2.me/theorems/51dc801b-cc3d-40de-a10a-88d880da1679
-- title:
--   Low-order measurement attainment and tensor-positive monotonicity
-- statement:
--   For every order 1/2≤α<1, the new divergence D̃α on density-operator pairs over all finite dimensions has asymptotic measurement attainment and is monotone under every trace-preserving complex-linear map whose positive tensor powers are all positive:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   $$
--   \mathrm{AAM}(\widetilde D_\alpha)\quad\text{and}\quad\mathrm{EPPMON}(\widetilde D_\alpha).
--   $$
--
--   This records the low-order consequences of the cited pinching and CPTP results for this specific additive Renyi family.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 22, However, when combined with MON for α ∈ [1/2, 1), derived by other methods as mentioned above, it

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.22: Low-order measurement attainment and tensor-positive monotonicity. The paragraph combines cited AAP [21] and MON [13] with the paper argument. This particular Renyi family has tensor additivity, unlike the unrestricted functions in defective (A3). -/
theorem low_order_attainability_and_tensor_monotonicity (alpha : ℝ) (ha0 : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    AAM (newFamily alpha) ∧ EPPMON (newFamily alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
