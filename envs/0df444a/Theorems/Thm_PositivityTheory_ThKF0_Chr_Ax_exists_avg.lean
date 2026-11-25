-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_exists_avg
-- name    : PositivityTheory.ThKF0.Chr.Ax.exists_avg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:01.270196+00:00
-- url     : https://prove2.me/theorems/3915a484-58dd-4ab2-9111-640f8a6a853f
-- title:
--   Ax: exists avg
-- statement:
--   The Ax construction uses the exists avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L183-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean#L183-L264

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

theorem PositivityTheory.ThKF0.Chr.Ax.exists_avg (h : Ax C ψ) (hI : AxInt C) (hS : IsSp S) (hj : Function.Injective j)
    (hE : IsE C ψ (dbS S) (Sum.map j j) E) {l : ((κ₁ ⊕ κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm (κ₁ ⊕ κ₁))
    (hinv : ∀ w : V R κ₁, ∀ φ ∈ C.sp (κ₁ ⊕ κ₁), l (schr ψ (dv w w) φ) = l φ) (hc : Cyc C ψ l)
    (ρ : Type) [Fintype ρ] (i : ρ → κ) (hi : Function.Injective i) (hij : ∀ k, (∃ a, i a = k) ↔ ¬ ∃ a, j a = k) :
    ∃ L ∈ C.adm (κ ⊕ κ), (∃ φ ∈ C.sp (κ ⊕ κ), L φ ≠ 0) ∧ (∀ w : V R κ, ∀ φ ∈ C.sp (κ ⊕ κ), L (schr ψ (dv w w) φ) = L φ) ∧
      ∀ (O : Module.End ℂ ((κ ⊕ κ → R) → ℂ)) (a : ℂ) (g : (ρ → R) ≃ₗ[R] (ρ → R)), a ≠ 0 → (∀ φ ∈ C.sp (κ ⊕ κ), O φ ∈ C.sp (κ ⊕ κ)) →
        (∀ u, ∀ φ ∈ C.sp (κ ⊕ κ), O (schr ψ (dv (S.symm (Function.extend i u 0, 0)) (S.symm (Function.extend i u 0, 0))) φ) =
          schr ψ (dv (S.symm (Function.extend i (g u) 0, 0)) (S.symm (Function.extend i (g u) 0, 0))) (O φ)) →
        (∀ φ ∈ C.sp (κ ⊕ κ), l (E (O φ)) = a * l (E φ)) →
        ∀ φ ∈ C.sp (κ ⊕ κ), L (O φ) = a * ((C.modu (LinearEquiv.det g) : ℝ) : ℂ) * L φ := by sorry
