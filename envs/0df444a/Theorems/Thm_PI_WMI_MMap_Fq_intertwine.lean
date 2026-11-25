-- Prove2me | Theorems.Thm_PI_WMI_MMap_Fq_intertwine
-- name    : PI.WMI.MMap.Fq_intertwine
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:39.698695+00:00
-- url     : https://prove2.me/theorems/5743fa91-116f-42f2-9a5e-a452f5c10402
-- title:
--   MMap: Fq intertwine
-- statement:
--   The MMap construction uses the Fq intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/ModelMap.lean#L148-L151

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

theorem PI.WMI.MMap.Fq_intertwine (g : Matrix (Fin N) (Fin N) ℂ) (x : V) :
    Fq hP v0 (P g x) = rowAct ℂ (n := N) gᵀ (Fq hP v0 x) := by sorry
