-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_lev_scalar2
-- name    : PositivityTheory.ThKF0.Chr.lev_scalar2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:04:42.5132+00:00
-- url     : https://prove2.me/theorems/42a0f3ee-52d1-4f25-8705-8750f65af685
-- title:
--   Chr: lev scalar2
-- statement:
--   The Chr construction uses the lev scalar2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/LevScalar2.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/LevScalar2.lean#L17-L40

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
omit [DecidableEq α]

theorem PositivityTheory.ThKF0.Chr.lev_scalar2 (h : Ax C ψ) (hS : IsSp S) (hj : Function.Injective j) (he : IsE C ψ S j e)
    {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA J₁) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ a : Matrix α ν E, u = z * ιᵀ + a * Xᵀ)
    {om : UG c J →* Module.End ℂ ((κ → R) → ℂ)} {om₁ : UG c J₁ →* Module.End ℂ ((κ₁ → R) → ℂ)}
    (hs : IsSplitting C ψ d (actB c) om) (hs₁ : IsSplitting C ψ d₁ (actB c) om₁)
    (m : UG c J) (g : UG c J₁) (t : Matrix ν ν E) (n : Matrix ν β₁ E)
    (h1 : m.1.1 * ι = ι * g.1.1 + X * n) (h2 : m.1.1 * X = X * t) :
    ∃ a : ℂ, ∀ φ ∈ C.sp κ, e (om m φ) = a • om₁ g (e φ) := by sorry
