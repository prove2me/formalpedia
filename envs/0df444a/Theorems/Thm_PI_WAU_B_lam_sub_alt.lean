-- Prove2me | Theorems.Thm_PI_WAU_B_lam_sub_alt
-- name    : PI.WAU.B.lam_sub_alt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:06.593605+00:00
-- url     : https://prove2.me/theorems/c236048c-173b-44df-bf3c-62f901340629
-- title:
--   B: lam sub alt
-- statement:
--   The B construction uses the lam sub alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L167-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L167-L176

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
variable {k : ℕ} {m : Fin k → Fin n → E}

theorem PI.WAU.B.lam_sub_alt {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : w ∈ Tset (F := F) m := by sorry
