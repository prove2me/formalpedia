-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_ext_inr
-- name    : PositivityTheory.ThKF0.Chr.ext_inr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:06:01.961823+00:00
-- url     : https://prove2.me/theorems/a79ffd29-a8c3-5f20-a97f-628c693dbdd6
-- title:
--   Chr: ext inr
-- statement:
--   The Chr construction uses the ext inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L125-L129

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

theorem PositivityTheory.ThKF0.Chr.ext_inr (x : κ₁ → R) : Function.extend (Sum.inr : κ₁ → κ ⊕ κ₁) x 0 = Sum.elim (0 : κ → R) x := by sorry
