-- Prove2me | Theorems.Thm_PI_ScRefExists_GWG_hG_zsmul_right
-- name    : PI.ScRefExists.GWG.hG_zsmul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:31.301247+00:00
-- url     : https://prove2.me/theorems/d1abc3d1-f2db-4e99-bc2f-780faf9225c5
-- title:
--   GWG: h G zsmul right
-- statement:
--   The GWG construction uses the h G zsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/GWGlue.lean#L45-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
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
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.GWG.hG_zsmul_right (q : ℤ) (x y : Fin I.n → I.E) : hG I x (q • y) = (q : I.E) * hG I x y := by sorry
