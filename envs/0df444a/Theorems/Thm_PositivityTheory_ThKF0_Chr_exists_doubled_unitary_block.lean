-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Chr_exists_doubled_unitary_block
-- name    : PositivityTheory.ThKF0.Chr.exists_doubled_unitary_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:59.635904+00:00
-- url     : https://prove2.me/theorems/cee3feb5-9a34-4632-bf85-86a2b7890710
-- title:
--   Chr: exists doubled unitary block
-- statement:
--   The Chr construction uses the exists doubled unitary block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/ExistsDoubledUnitaryBlock.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/ExistsDoubledUnitaryBlock.lean#L62-L70

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
omit [Invertible (2 : R)]

theorem PositivityTheory.ThKF0.Chr.exists_doubled_unitary_block {J : Matrix β β E} (g : UG c J) : ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by sorry
