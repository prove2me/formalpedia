-- Prove2me | Theorems.Thm_PI_WAU_B_mulVec_lam
-- name    : PI.WAU.B.mulVec_lam
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:33.320418+00:00
-- url     : https://prove2.me/theorems/0c97ac4b-437f-489c-ba30-9cfa3a5cb079
-- title:
--   B: mul Vec lam
-- statement:
--   The B construction uses the mul Vec lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L178-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L178-L187

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

theorem PI.WAU.B.mulVec_lam {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    (P : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))
    (hP : ∀ j, P *ᵥ ivec (F := F) (m j) ∈ lamAf (F := F) L) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : P *ᵥ w ∈ lamAf (F := F) L := by sorry
