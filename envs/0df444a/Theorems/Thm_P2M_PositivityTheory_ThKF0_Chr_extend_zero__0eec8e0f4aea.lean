-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
-- name    : P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:02.463834+00:00
-- url     : https://prove2.me/theorems/c8ae62cc-1a30-410a-9466-ee074f796ca3
-- title:
--   P2 M Positivity Theory Th KF0 Chr extend zero  0eec8e0f4aea: P2 M Positivity Theory Th KF0 Chr extend zero  0eec8e0f4aea
-- statement:
--   The P2 M Positivity Theory Th KF0 Chr extend zero  0eec8e0f4aea construction uses the P2 M Positivity Theory Th KF0 Chr extend zero  0eec8e0f4aea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L149-L154

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
omit [Invertible (2 : R)] [Fintype κ] [Fintype κ₁]

theorem P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea {j : κ₁ → κ} (hj : Function.Injective j) : Function.extend j (0 : κ₁ → R) 0 = 0 := by sorry

alias «PositivityTheory».«ThKF0».«Chr».«extend_zero'» := P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
