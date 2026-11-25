-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_avgF_mem
-- name    : ReciprocityTheory.PGsh.Up.avgF_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:42.195746+00:00
-- url     : https://prove2.me/theorems/1978900c-9e28-4fd2-8727-8f74a425173f
-- title:
--   Up: avg F mem
-- statement:
--   The Up construction uses the avg F mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean#L23-L31

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

theorem ReciprocityTheory.PGsh.Up.avgF_mem {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    {F : Nb p g → C} (hF : F ∈ H.AA.carrier) : avgF β H U i c₀ F ∈ H.AA.carrier := by sorry
