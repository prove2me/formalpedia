-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_E
-- name    : PositivityTheory.ThKF0.Chr.Ax.exists_E
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:18.801921+00:00
-- url     : https://prove2.me/theorems/029f2ca3-a64a-4705-8951-93643cde337e
-- title:
--   Ax: exists E
-- statement:
--   The Ax construction uses the exists E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L178-L181

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

theorem PositivityTheory.ThKF0.Chr.Ax.exists_E (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) {j : κ₁ → κ} (hj : Function.Injective j) :
    ∃ e, IsE C ψ S j e := by sorry
