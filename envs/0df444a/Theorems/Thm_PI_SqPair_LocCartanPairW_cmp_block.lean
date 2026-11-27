-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_block
-- name    : PI.SqPair.LocCartanPairW.cmp_block
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:47:49.051446+00:00
-- url     : https://prove2.me/theorems/aabc1e63-d9d8-428e-977e-75124acdb99a
-- title:
--   Loc Cartan Pair W: cmp block
-- statement:
--   The Loc Cartan Pair W construction uses the cmp block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L53-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpBlock.lean#L53-L101

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

theorem PI.SqPair.LocCartanPairW.cmp_block [IsDomain R] {ι μ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ]
    [DecidableEq μ] [Fintype κ] [DecidableEq κ]
    (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (J : Matrix μ μ R) (hJ : J.det ≠ 0) (A₁ A₁' : Matrix κ κ R)
    (u u' : Matrix ι (μ ⊕ κ) R) (v : Matrix (μ ⊕ κ) ι R) (hvu : v * u = 1) (huv : u * v = 1)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks J 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks J 0 0 A₁')
    (c : μ → R) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ r i, (h * u') r (Sum.inl i) = c i * u r (Sum.inl i)) :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal c) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by sorry
