-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_length_quot_eq_relfinrank_5f604ca6cb09
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_length_quot_eq_relfinrank_5f604ca6cb09
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:47:29.19313+00:00
-- url     : https://prove2.me/theorems/3391d3e7-9f86-4e21-8e68-7ba273f1eef3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac length quot eq relfinrank 5f604ca6cb09: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac length quot eq relfinrank 5f604ca6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac length quot eq relfinrank 5f604ca6cb09 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac length quot eq relfinrank 5f604ca6cb09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L152-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L152-L199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_length_quot_eq_relfinrank_5f604ca6cb09 {F : Type} [Field F] [Algebra F Ω] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔪 : Ideal B) (ρ : B →+* Ω) (hker : ∀ b, ρ b = 0 ↔ b ∈ 𝔪)
    (L₀ L : IntermediateField F Ω) (hle : L₀ ≤ L) (hB : ∀ b, ρ b ∈ L) (hBs : ∀ y ∈ L, ∃ b, ρ b = y)
    (hA : ∀ a, ρ (algebraMap A B a) ∈ L₀) (hAs : ∀ y ∈ L₀, ∃ a, ρ (algebraMap A B a) = y) :
    Module.length A (B ⧸ 𝔪) = (IntermediateField.relfinrank L₀ L : ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«length_quot_eq_relfinrank» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_length_quot_eq_relfinrank_5f604ca6cb09
