-- Prove2me | Theorems.Thm_PI_ScRefExists_LG_int_mem_intAd
-- name    : PI.ScRefExists.LG.int_mem_intAd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:38:16.607525+00:00
-- url     : https://prove2.me/theorems/38246661-7840-4e12-b878-cb469ffdd740
-- title:
--   LG: int mem int Ad
-- statement:
--   The LG construction uses the int mem int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
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
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.ScRefExists.LG.int_mem_intAd (r : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by sorry
