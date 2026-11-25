-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_schur
-- name    : PositivityTheory.ThKF0.Chr.Ax.schur
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:04:44.415395+00:00
-- url     : https://prove2.me/theorems/c908abcc-f10a-4c85-9f4c-f84fabf720a6
-- title:
--   Ax: schur
-- statement:
--   The Ax construction uses the schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L65-L73

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

theorem PositivityTheory.ThKF0.Chr.Ax.schur (h : Ax C ψ) (T : Module.End ℂ ((κ → R) → ℂ)) (ha : Chr.ev0 R κ ∘ₗ T ∈ C.adm κ)
    (hc : ∀ w, ∀ φ ∈ C.sp κ, T (schr ψ w φ) = schr ψ w (T φ)) : ∃ a : ℂ, ∀ φ ∈ C.sp κ, T φ = a • φ := by sorry
