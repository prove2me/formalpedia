-- Prove2me | Theorems.Thm_PI_ScRefExists_Id_iE_alg
-- name    : PI.ScRefExists.Id.iE_alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:26:45.140983+00:00
-- url     : https://prove2.me/theorems/94ff941e-8dd0-57b4-ad8d-c3071a7a8339
-- title:
--   Id: i E alg
-- statement:
--   The Id construction uses the i E alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemTen.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/IdemTen.lean#L44-L46

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

theorem PI.ScRefExists.Id.iE_alg (x : I.F) : iE I (algebraMap I.F I.E x) = iA I (algebraMap I.F (Af I.F) x) := by sorry
