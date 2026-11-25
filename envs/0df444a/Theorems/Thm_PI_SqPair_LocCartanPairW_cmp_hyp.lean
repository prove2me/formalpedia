-- Prove2me | Theorems.Thm_PI_SqPair_LocCartanPairW_cmp_hyp
-- name    : PI.SqPair.LocCartanPairW.cmp_hyp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:25.153679+00:00
-- url     : https://prove2.me/theorems/9eac8bad-8ec1-44f6-a1d6-6b55301d82e8
-- title:
--   Loc Cartan Pair W: cmp hyp
-- statement:
--   The Loc Cartan Pair W construction uses the cmp hyp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/CmpPair.lean#L67-L76

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

theorem PI.SqPair.LocCartanPairW.cmp_hyp [IsDomain R] {ι : Type*} [Fintype ι] (A A' h : Matrix ι ι R) (s : R) (hs : s ≠ 0)
    (hh : (h.map σ)ᵀ * A * h = s • A') (c₁ c₂ : R) (hc : σ c₁ * c₂ = s)
    (x₁ y₁ v₁ w₁ : ι → R) (hv : h *ᵥ v₁ = c₁ • x₁) (hw : h *ᵥ w₁ = c₂ • y₁)
    (hxx : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ x₁) = 0) (hyy : (fun i => σ (y₁ i)) ⬝ᵥ (A *ᵥ y₁) = 0)
    (hxy : (fun i => σ (x₁ i)) ⬝ᵥ (A *ᵥ y₁) = 1) :
    (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ v₁) = 0 ∧ (fun i => σ (w₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 0 ∧
      (fun i => σ (v₁ i)) ⬝ᵥ (A' *ᵥ w₁) = 1 := by sorry
