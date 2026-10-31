-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_quasiFreeCCR_regular
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.quasiFreeCCR_regular
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:13:36.230993+00:00
-- url     : https://prove2.me/theorems/8947382e-502d-461f-b56f-9225883d4520
-- title:
--   Quasi-free CCR representations are regular
-- statement:
--   Let $Y$ be a real vector space with antisymmetric bilinear form $\omega$, and let $W:Y\to\mathcal U(H)$ satisfy the Weyl relations. Suppose there is a cyclic vector $\Psi$ and a real symmetric bilinear form $\eta$ such that
--   $$\langle\Psi,W(y)\Psi\rangle=\exp(-\eta(y,y)/4)\quad(y\in Y).$$
--   Then $W$ is regular:
--   $$t\longmapsto W(ty)v\text{ is continuous for every }y\in Y,\ v\in H.$$
--   Cyclicity means density of the complex span of the Weyl orbit. The characteristic identity at zero forces $\|\Psi\|=1$; neither regularity nor positivity of $\eta$ is assumed in place of the conclusion.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 38, Theorem 37

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.38, Theorem 37: every cyclic quasi-free CCR representation is regular. -/
theorem quasiFreeCCR_regular (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hanti : Antisymmetric omega) (W : Y → H →L[ℂ] H)
    (hW : IsCCR omega W) (hq : QuasiFreeCCR W) : WeylRegular W := by sorry

end QAlgorithms.Papers.Independent.Intake100.P23

end
