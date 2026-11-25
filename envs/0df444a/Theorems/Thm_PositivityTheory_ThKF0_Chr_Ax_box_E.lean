-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_box_E
-- name    : PositivityTheory.ThKF0.Chr.Ax.box_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:02.912792+00:00
-- url     : https://prove2.me/theorems/02f9fd45-ec6e-48f6-81a6-7fa6c45110ef
-- title:
--   Ax: box E
-- statement:
--   The Ax construction uses the box E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L131-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L131-L167

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}

theorem PositivityTheory.ThKF0.Chr.Ax.box_E (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    (hE : IsE C ψ (dbS S) (Sum.map j j) E) : ∀ φ₂ ∈ C.sp κ, ∃ A ∈ C.sp κ₁, ∀ φ₁ ∈ C.sp κ, E (boxFun φ₁ φ₂) = boxFun (e φ₁) A := by sorry
