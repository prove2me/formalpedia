-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_corollary5
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.corollary5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:35:23.980675+00:00
-- url     : https://prove2.me/theorems/cdc49e63-cc67-4071-aad2-a3f186b3cf77
-- title:
--   Operational PPT distillation is bounded by Rains
-- statement:
--   Let $\rho$ be a density operator on nonzero finite-dimensional $A\otimes B$ with fixed product bases. Define $\mathrm{PPT}'=\{\sigma\ge0:\|\sigma^{T_B}\|_1\le1\}$ and
--
--   $$R(\rho)=\inf_{\sigma\in\mathrm{PPT}'}D(\rho\|\sigma),\qquad D(\rho\|\sigma)=\operatorname{Tr}\rho(\log_2\rho-\log_2\sigma),$$
--
--   where relative entropy is $+\infty$ on support failure. Let $E_{D,\mathrm{PPT}}$ be the supremum of nonnegative rates achievable from independent copies by completely PPT-preserving CPTP maps with vanishing trace-norm error and integer-rounded output rank. Then
--
--   $$E_{D,\mathrm{PPT}}(\rho)\le R(\rho).$$
--
--   This is the known Rains bound [15,60], reproved in this paper; no double-limit existence is assumed.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 7, Corollary 5: asymptotic PPT distillability is bounded by Rains

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Corollary 5, arXiv:1706.06221v3, PDF p.7 (Rains [15,60], reproved here).
The left side uses operational vanishing trace-norm error, not an assumed double limit. -/
theorem corollary5 {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    pptDistillable rho ≤ rains rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
