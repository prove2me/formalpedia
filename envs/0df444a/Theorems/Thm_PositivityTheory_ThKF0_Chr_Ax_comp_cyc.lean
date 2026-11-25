-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_comp_cyc
-- name    : PositivityTheory.ThKF0.Chr.Ax.comp_cyc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:14.875804+00:00
-- url     : https://prove2.me/theorems/1a8a9cce-134c-434e-b31b-93947169628a
-- title:
--   Ax: comp cyc
-- statement:
--   The Ax construction uses the comp cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L202-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/SchrodingerApplyZeroOfFst.lean#L202-L208

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

theorem PositivityTheory.ThKF0.Chr.Ax.comp_cyc (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {l : ((κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : Cyc C ψ l) : ∀ φ ∈ C.sp κ, φ ≠ 0 → ∃ w w', l (e (schr ψ w' (schr ψ w φ))) ≠ 0 := by sorry
