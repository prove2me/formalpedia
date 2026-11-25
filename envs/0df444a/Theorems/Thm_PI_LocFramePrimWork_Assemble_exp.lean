-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Assemble_exp
-- name    : PI.LocFramePrimWork.Assemble_exp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:35.144817+00:00
-- url     : https://prove2.me/theorems/b2819fe1-a9a5-4041-bbb2-469b8a19c967
-- title:
--   Loc Frame Prim Work: Assemble exp
-- statement:
--   The Loc Frame Prim Work construction uses the Assemble exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean#L95-L97

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

theorem PI.LocFramePrimWork.Assemble_exp {r : ℕ} (a : Fin r) :
    (-((r : ℤ) - ((a : ℕ) : ℤ))) = -(((r - (a : ℕ) : ℕ)) : ℤ) := by sorry
