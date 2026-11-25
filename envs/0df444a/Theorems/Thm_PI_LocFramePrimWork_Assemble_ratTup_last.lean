-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_ratTup_last
-- name    : PI.LocFramePrimWork.Assemble_ratTup_last
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:50.456944+00:00
-- url     : https://prove2.me/theorems/b71ea346-57d4-4c4a-9db7-a0ea3d46d405
-- title:
--   Loc Frame Prim Work: Assemble rat Tup last
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble rat Tup last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L77-L80

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

theorem PI.LocFramePrimWork.Assemble_ratTup_last {r : ℕ} (e : Fin r → Fin n → E) (z : Fin n → E) :
    ratTup (F := F) (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E) (Fin.last r) =
      ratV (F := F) (Fv F v) z := by sorry
