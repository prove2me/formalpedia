-- Prove2me | Theorems.Thm_PI_WMI_MMap_Fq_colAdd
-- name    : PI.WMI.MMap.Fq_colAdd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:01:01.339818+00:00
-- url     : https://prove2.me/theorems/fbdb2e64-04a9-5f0d-a435-a1bb772667ce
-- title:
--   MMap: Fq col Add
-- statement:
--   The MMap construction uses the Fq col Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L153-L158

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
open PI.WMI.MMap
variable {N : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {P : Matrix (Fin N) (Fin N) ℂ → (V →ₗ[ℂ] V)} (hP : IsPolyMon P) (v0 : V)

theorem PI.WMI.MMap.Fq_colAdd
    (hlow : ∀ a b : Fin N, a < b → ∀ (c : ℂ) (x : V), ⟪v0, P (1 + Matrix.single b a c) x⟫_ℂ = ⟪v0, x⟫_ℂ)
    (l j : Fin N) (hlj : l < j) (c : ℂ) (x : V) :
    colAdd ℂ (r := N) l j c (Fq hP v0 x) = Fq hP v0 x := by sorry
