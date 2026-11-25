-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_decay_of_vanishing_at_cusps__97d5fc80e808
-- name    : P2M_GlobalTheory_T_decay_of_vanishing_at_cusps__97d5fc80e808
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:28.941802+00:00
-- url     : https://prove2.me/theorems/383c64fa-3dd6-4efd-a9e3-f4614c061d00
-- title:
--   P2 M Global Theory T decay of vanishing at cusps  97d5fc80e808: P2 M Global Theory T decay of vanishing at cusps  97d5fc80e808
-- statement:
--   The P2 M Global Theory T decay of vanishing at cusps  97d5fc80e808 construction uses the P2 M Global Theory T decay of vanishing at cusps  97d5fc80e808 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCuspsStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DecayOfVanishingAtCuspsStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCuspsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_decay_of_vanishing_at_cusps__97d5fc80e808 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by sorry

alias «GlobalTheory».«T».«decay_of_vanishing_at_cusps'» := P2M_GlobalTheory_T_decay_of_vanishing_at_cusps__97d5fc80e808
