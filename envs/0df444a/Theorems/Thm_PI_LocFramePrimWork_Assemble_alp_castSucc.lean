-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_alp_castSucc
-- name    : PI.LocFramePrimWork.Assemble_alp_castSucc
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:16.721583+00:00
-- url     : https://prove2.me/theorems/fc24a880-8bcf-54ac-b7ba-c484083a908f
-- title:
--   Loc Frame Prim Work: Assemble alp cast Succ
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble alp cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L82-L84

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

theorem PI.LocFramePrimWork.Assemble_alp_castSucc {r : ℕ} (a : Fin r) :
    alp v r (Fin.castSucc a) = (dV v)⁻¹ ^ (r - (a : ℕ)) := by sorry
