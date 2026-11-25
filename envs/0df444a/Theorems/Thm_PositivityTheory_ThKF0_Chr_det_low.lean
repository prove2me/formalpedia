-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_det_low
-- name    : PositivityTheory.ThKF0.Chr.det_low
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:13.929884+00:00
-- url     : https://prove2.me/theorems/efb1dda7-536f-4f98-91fe-059a8f0cf24c
-- title:
--   Chr: det low
-- statement:
--   The Chr construction uses the det low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/LevScalar2.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/LevScalar2.lean#L49-L51

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_LevScalar2
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
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β β₁ ν κ κ₁ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁]
  [Fintype ν] [DecidableEq ν] [Fintype κ] [Fintype κ₁] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E}
  {JA : Matrix α α E} {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {ι : Matrix β β₁ E} {X : Matrix β ν E}
  {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}

theorem PositivityTheory.ThKF0.Chr.det_low {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (n : Matrix b a E) (t : GL b E) :
    GeneralLinearGroup.det (low n t) = GeneralLinearGroup.det t := by sorry
