-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_det_diag_ne
-- name    : PI.SqPair.LocCartanPairW.cmp_det_diag_ne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:12.749382+00:00
-- url     : https://prove2.me/theorems/f8c837b3-e3b1-5877-baa4-9554232e353f
-- title:
--   Loc Cartan Pair W: cmp det diag ne
-- statement:
--   The Loc Cartan Pair W construction uses the cmp det diag ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L41-L47

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

theorem PI.SqPair.LocCartanPairW.cmp_det_diag_ne [IsDomain R] {μ : Type*} [Fintype μ] [DecidableEq μ] (J : Matrix μ μ R)
    (hJ : J.det ≠ 0) (c : μ → R) (hc : ∀ i, c i ≠ 0) :
    (((diagonal c).map σ)ᵀ * J).det ≠ 0 := by sorry
