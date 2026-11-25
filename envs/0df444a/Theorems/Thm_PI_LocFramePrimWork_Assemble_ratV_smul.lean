-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_ratV_smul
-- name    : PI.LocFramePrimWork.Assemble_ratV_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:36.936491+00:00
-- url     : https://prove2.me/theorems/3fe70fa1-4531-4cf5-82c3-99e58b8f2981
-- title:
--   Loc Frame Prim Work: Assemble rat V smul
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble rat V smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L91-L93

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem PI.LocFramePrimWork.Assemble_ratV_smul (x : E) (y : Fin n → E) :
    inclR (F := F) (Fv F v) x • ratV (F := F) (Fv F v) y = ratV (F := F) (Fv F v) (x • y) := by sorry
