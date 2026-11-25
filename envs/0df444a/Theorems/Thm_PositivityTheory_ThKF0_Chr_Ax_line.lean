-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_line
-- name    : PositivityTheory.ThKF0.Chr.Ax.line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:55.64782+00:00
-- url     : https://prove2.me/theorems/3a899034-243a-4e5d-80a1-2f9f5cb3c25f
-- title:
--   Ax: line
-- statement:
--   The Ax construction uses the line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L75-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L75-L93

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

theorem PositivityTheory.ThKF0.Chr.Ax.line (h : Ax C ψ) {S : V R κ ≃ₗ[R] V R κ} (hS : IsSp S) {T : Module.End ℂ ((κ → R) → ℂ)} (hT : IsImp C ψ S T)
    {l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm κ) (hinv : ∀ w, (S w).1 = 0 → ∀ φ ∈ C.sp κ, l (schr ψ w φ) = l φ) :
    ∃ a : ℂ, ∀ φ ∈ C.sp κ, l φ = a * T φ 0 := by sorry
