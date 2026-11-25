-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_split
-- name    : PI.SqPair.LocCartanPairW.cmp_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:31.977878+00:00
-- url     : https://prove2.me/theorems/fe79f4b3-6997-4db6-90fc-ce7dc5b03730
-- title:
--   Loc Cartan Pair W: cmp split
-- statement:
--   The Loc Cartan Pair W construction uses the cmp split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L83-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L83-L160

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpPair
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

theorem PI.SqPair.LocCartanPairW.cmp_split [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (c₁ c₂ : R) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (x y v₁ w₁ : ι → R)
    (hv : h *ᵥ v₁ = c₁ • x) (hw : h *ᵥ w₁ = c₂ • y)
    (u u' : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ A₁' : Matrix κ κ R)
    (huv : u * v = 1) (hvu : v * u = 1)
    (hu0 : ∀ i, u i (.inl 0) = x i) (hu1 : ∀ i, u i (.inl 1) = y i)
    (hu0' : ∀ i, u' i (.inl 0) = v₁ i) (hu1' : ∀ i, u' i (.inl 1) = w₁ i)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks !![0, 1; 1, 0] 0 0 A₁') :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal ![c₁, c₂]) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by sorry
