-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_conjT_mul
-- name    : PI.SqPair.LocCartanPairW.cmp_conjT_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:07.130634+00:00
-- url     : https://prove2.me/theorems/670fb45c-3344-5f9d-b5f4-4c084938dfe4
-- title:
--   Loc Cartan Pair W: cmp conj T mul
-- statement:
--   The Loc Cartan Pair W construction uses the cmp conj T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem PI.SqPair.LocCartanPairW.cmp_conjT_mul {l m n : Type*} [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    ((M * N).map σ)ᵀ = (N.map σ)ᵀ * (M.map σ)ᵀ := by sorry
