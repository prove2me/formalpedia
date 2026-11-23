-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_eig
-- name    : ReciprocityTheory.PGsh.Up.avgF_eig
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:17.847995+00:00
-- url     : https://prove2.me/theorems/9e4cea09-7c69-457e-b4cb-52ca4adb5a3c
-- title:
--   Up: avg F eig
-- statement:
--   The Up construction uses the avg F eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean#L76-L90

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

theorem ReciprocityTheory.PGsh.Up.avgF_eig (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H)
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (h1 : H.ρ (β 1) = 1)
    {i : Fin U.m} (hi : U.εT i ≠ 0) (c₀ : R) (F : Nb p g → C) (δ : G) (y : Nb p g) :
    avgF β H U i c₀ F (nbAct H (β δ) y) =
      algebraMap R C (U.sg i (β δ)) * avgF β H U i c₀ F y := by sorry
