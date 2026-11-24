-- Prove2me | Theorems.Thm_PI_WAU_B_smulO_mem
-- name    : PI.WAU.B.smulO_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:38.728984+00:00
-- url     : https://prove2.me/theorems/49b1c05c-b1c7-4e94-8ff7-d544b75ad4d0
-- title:
--   B: smul O mem
-- statement:
--   The B construction uses the smul O mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L70-L72

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem PI.WAU.B.smulO_mem {L : Submodule (𝓞 E) (Fin n → E)} {o : E ⊗[F] Af F} (ho : o ∈ IntAf F E)
    {w : Fin n → E ⊗[F] Af F} (hw : w ∈ lamAf (F := F) L) : o • w ∈ lamAf (F := F) L := by sorry
