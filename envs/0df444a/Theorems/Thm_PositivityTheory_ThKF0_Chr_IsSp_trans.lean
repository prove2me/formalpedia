-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans
-- name    : PositivityTheory.ThKF0.Chr.IsSp.trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:38.18424+00:00
-- url     : https://prove2.me/theorems/ea046291-b1d8-4d07-bd1b-0c8d06fab7d1
-- title:
--   Is Sp: trans
-- statement:
--   The Is Sp construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L40-L41

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
omit [Invertible (2 : R)]

theorem PositivityTheory.ThKF0.Chr.IsSp.trans {S S' : V R κ ≃ₗ[R] V R κ} (h : IsSp S) (h' : IsSp S') : IsSp (S.trans S') := by sorry
