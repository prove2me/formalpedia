-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_dbl
-- name    : PositivityTheory.ThKF0.Chr.rel_dbl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:34.86546+00:00
-- url     : https://prove2.me/theorems/9566b181-4401-42f7-a623-3feb953896f3
-- title:
--   Chr: rel dbl
-- statement:
--   The Chr construction uses the rel dbl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/ExistsDoubledUnitaryBlock.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/ExistsDoubledUnitaryBlock.lean#L43-L59

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_ExistsDoubledUnitaryBlock
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
omit [DecidableEq α] [Invertible (2 : R)] [DecidableEq ν]

theorem PositivityTheory.ThKF0.Chr.rel_dbl (hj : Function.Injective j) {d : Darboux (symp c ξ JA J) κ} {d₁ : Darboux (symp c ξ JA J₁) κ₁}
    (hrel : ∀ u z, Rel S j (d.e u) (d₁.e z) ↔ ∃ a : Matrix α ν E, u = z * ιᵀ + a * Xᵀ)
    {dd : Darboux (symp c ξ JA (dbl J)) (κ ⊕ κ)} {dd₁ : Darboux (symp c ξ JA (dbl J₁)) (κ₁ ⊕ κ₁)}
    (hd : IsDblCoord c ξ JA J d dd) (hd₁ : IsDblCoord c ξ JA J₁ d₁ dd₁) (u z) :
    Rel (dbS S) (Sum.map j j) (dd.e u) (dd₁.e z) ↔ ∃ a : Matrix α (ν ⊕ ν) E, u = z * (dd2 ι)ᵀ + a * (dd2 X)ᵀ := by sorry
