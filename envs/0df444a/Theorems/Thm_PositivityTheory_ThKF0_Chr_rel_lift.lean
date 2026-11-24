-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_lift
-- name    : PositivityTheory.ThKF0.Chr.rel_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:21.141816+00:00
-- url     : https://prove2.me/theorems/f17ee3ed-c3d4-4916-a9dc-e9253868ff94
-- title:
--   Chr: rel lift
-- statement:
--   The Chr construction uses the rel lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L157-L160

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

theorem PositivityTheory.ThKF0.Chr.rel_lift {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} (hj : Function.Injective j) (w₁ : V R κ₁) :
    Rel S j (S.symm (Function.extend j w₁.1 0, Function.extend j w₁.2 0)) w₁ := by sorry
