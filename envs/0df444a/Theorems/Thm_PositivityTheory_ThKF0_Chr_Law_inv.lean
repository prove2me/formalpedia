-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Law_inv
-- name    : PositivityTheory.ThKF0.Chr.Law.inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:02.519599+00:00
-- url     : https://prove2.me/theorems/4f34fc63-5c3a-4cac-acaf-c37d467438b0
-- title:
--   Law: inv
-- statement:
--   The Law construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L185-L188

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ResAdm
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
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
variable {R : Type} [CommRing R] [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
  {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e e' : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}

theorem PositivityTheory.ThKF0.Chr.Law.inv (he : Law C ψ S j e) (hj : Function.Injective j) (w : V R κ) (hw : (S w).1 = 0) (φ : (κ → R) → ℂ)
    (hφ : φ ∈ C.sp κ) : (ev0 R κ₁ ∘ₗ e) (schr ψ w φ) = (ev0 R κ₁ ∘ₗ e) φ := by sorry
