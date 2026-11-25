-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_ext_inl
-- name    : PositivityTheory.ThKF0.Chr.ext_inl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:06:02.52032+00:00
-- url     : https://prove2.me/theorems/afc7b884-b170-5a63-8b5e-809d1f287150
-- title:
--   Chr: ext inl
-- statement:
--   The Chr construction uses the ext inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L118-L122

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
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]

theorem PositivityTheory.ThKF0.Chr.ext_inl (x : κ → R) : Function.extend (Sum.inl : κ → κ ⊕ κ₁) x 0 = Sum.elim x 0 := by sorry
