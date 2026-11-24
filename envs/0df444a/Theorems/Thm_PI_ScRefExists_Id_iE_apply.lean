-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_iE_apply
-- name    : PI.ScRefExists.Id.iE_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:35:39.442942+00:00
-- url     : https://prove2.me/theorems/ad1a8f3b-3454-42d6-8a8e-28d79763fbd0
-- title:
--   Id: i E apply
-- statement:
--   The Id construction uses the i E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemTen.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemTen.lean#L41-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemLiftOfSteps
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_IdemTen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Id
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.Id.iE_apply (e : I.E) : iE I e = e ⊗ₜ[I.F] (1 : Af I.F) := by sorry
