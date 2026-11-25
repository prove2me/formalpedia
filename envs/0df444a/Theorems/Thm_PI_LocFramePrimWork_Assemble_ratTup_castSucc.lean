-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_ratTup_castSucc
-- name    : PI.LocFramePrimWork.Assemble_ratTup_castSucc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:27.217044+00:00
-- url     : https://prove2.me/theorems/19891e6a-22d5-5f90-b3ee-5dca078ad393
-- title:
--   Loc Frame Prim Work: Assemble rat Tup cast Succ
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble rat Tup cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L72-L75

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

theorem PI.LocFramePrimWork.Assemble_ratTup_castSucc {r : ℕ} (e : Fin r → Fin n → E) (z : Fin n → E) (a : Fin r) :
    ratTup (F := F) (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E) (Fin.castSucc a) =
      ratV (F := F) (Fv F v) (e a) := by sorry
