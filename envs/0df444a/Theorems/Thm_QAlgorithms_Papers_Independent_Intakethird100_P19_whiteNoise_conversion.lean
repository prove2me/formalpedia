-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_whiteNoise_conversion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.whiteNoise_conversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:35:31.888935+00:00
-- url     : https://prove2.me/theorems/0a333812-fc8e-4b5d-bb81-ff522bbff925
-- title:
--   Lemma 8: corrected white-noise conversion criterion
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $k,d\ge2$, with pure states $\psi$ on $k\times k$ and $\varphi$ on $d\times d$, and decreasing squared Schmidt coefficients $\lambda_i,\mu_i$. Define
--
--   $$\Lambda(X)=\operatorname{Tr}(\psi X)\varphi+\operatorname{Tr}((I_{k^2}-\psi)X)\frac{I_{d^2}}{d^2}.$$
--
--   This is a channel and is non-entangling if $(1+d^2\sqrt{\mu_1\mu_2})\lambda_1\le1$. Under this condition it is also dually non-entangling if
--
--   $$(d^2\mu_1-1)\sqrt{\lambda_1\lambda_2}\le1.$$
--
--   Dually non-entangling means that both the channel and its trace dual preserve separable positive operators.
--
--   The cross-multiplied inequalities retain product-state cases.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 11, Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Lemma 8, PDF pp.11-12, corrected from its proof: printed Eq.(8)
omits 1+ in the denominator. Use (1+d^2 sqrt(mu_1 mu_2))*lambda_1<=1.
Eq.(9) is cross-multiplied to include zero second Schmidt coefficients.
The printed Bell-to-Bell case violates PPT preservation of separable inputs. -/
theorem whiteNoise_conversion {k d : ℕ} (hk : 2 ≤ k) (hd : 2 ≤ d)
    (psi : UnitBipartiteKet k k) (phi : UnitBipartiteKet d d)
    (hfirst : (1 + (d : ℝ) ^ 2 * Real.sqrt (schmidtAt phi.ket 0 * schmidtAt phi.ket 1)) *
      schmidtAt psi.ket 0 ≤ 1) :
    let L := binaryMeasurePrepare psi.rho phi.rho (((d : ℂ) ^ 2)⁻¹ • (1 : Bip d d))
    IsChannel L ∧ NE L ∧
      (((d : ℝ) ^ 2 * schmidtAt phi.ket 0 - 1) *
        Real.sqrt (schmidtAt psi.ket 0 * schmidtAt psi.ket 1) ≤ 1 → DNE L) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
