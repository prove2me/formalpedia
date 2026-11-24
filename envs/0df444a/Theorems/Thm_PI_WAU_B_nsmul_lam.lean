-- Prove2me | Theorems.Thm_PI_WAU_B_nsmul_lam
-- name    : PI.WAU.B.nsmul_lam
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:25.662927+00:00
-- url     : https://prove2.me/theorems/7d4a9fad-24f4-4b84-83d5-1378703cfefd
-- title:
--   B: nsmul lam
-- statement:
--   The B construction uses the nsmul lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatVec.lean#L74-L77

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

theorem PI.WAU.B.nsmul_lam {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E ⊗[F] Af F} {N : ℕ}
    (hw : N • w ∈ lamAf (F := F) L) (M : ℕ) : (N * M) • w ∈ lamAf (F := F) L := by sorry
