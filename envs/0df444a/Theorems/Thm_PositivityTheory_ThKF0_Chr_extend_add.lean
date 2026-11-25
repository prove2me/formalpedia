-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_extend_add
-- name    : PositivityTheory.ThKF0.Chr.extend_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:54.339842+00:00
-- url     : https://prove2.me/theorems/863f775e-b0e9-50c2-943e-dc53bbc476c7
-- title:
--   Chr: extend add
-- statement:
--   The Chr construction uses the extend add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L140-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L140-L146

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

theorem PositivityTheory.ThKF0.Chr.extend_add {j : κ₁ → κ} (hj : Function.Injective j) (a b : κ₁ → R) :
    Function.extend j (a + b) 0 = Function.extend j a 0 + Function.extend j b 0 := by sorry
