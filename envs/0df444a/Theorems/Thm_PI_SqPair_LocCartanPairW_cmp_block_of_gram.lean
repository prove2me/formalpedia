-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_block_of_gram
-- name    : PI.SqPair.LocCartanPairW.cmp_block_of_gram
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:01.698797+00:00
-- url     : https://prove2.me/theorems/33b0a1b7-909e-5e85-9ba4-23d160dc3574
-- title:
--   Loc Cartan Pair W: cmp block of gram
-- statement:
--   The Loc Cartan Pair W construction uses the cmp block of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L16-L39

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

theorem PI.SqPair.LocCartanPairW.cmp_block_of_gram [IsDomain R] {μ κ : Type*} [Fintype μ] [Fintype κ] [DecidableEq μ]
    (M : Matrix (μ ⊕ κ) (μ ⊕ κ) R) (J : Matrix μ μ R) (A₁ A₁' : Matrix κ κ R) (s : R)
    (hM : (M.map σ)ᵀ * fromBlocks J 0 0 A₁ * M = s • fromBlocks J 0 0 A₁')
    (h21 : M.toBlocks₂₁ = 0)
    (hdet : (((M.toBlocks₁₁).map σ)ᵀ * J).det ≠ 0) :
    M.toBlocks₁₂ = 0 ∧ ((M.toBlocks₂₂).map σ)ᵀ * A₁ * M.toBlocks₂₂ = s • A₁' := by sorry
