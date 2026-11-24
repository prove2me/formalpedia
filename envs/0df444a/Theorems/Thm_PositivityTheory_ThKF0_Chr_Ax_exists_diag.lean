-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_diag
-- name    : PositivityTheory.ThKF0.Chr.Ax.exists_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:59.445703+00:00
-- url     : https://prove2.me/theorems/dd157c0e-db91-4831-9902-c3d1c2c812ab
-- title:
--   Ax: exists diag
-- statement:
--   The Ax construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L178-L181

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
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
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}

theorem PositivityTheory.ThKF0.Chr.Ax.exists_diag (h : Ax C ψ) (κ : Type) [Fintype κ] : ∃ l ∈ C.adm (κ ⊕ κ),
    (∀ w : V R κ, ∀ φ ∈ C.sp (κ ⊕ κ), l (schr ψ (dv w w) φ) = l φ) ∧ Cyc C ψ l := by sorry
