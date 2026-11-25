-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_eq_of_normalised_a7ba18fcd80f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_eq_of_normalised_a7ba18fcd80f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:54:34.192093+00:00
-- url     : https://prove2.me/theorems/b46593f0-d188-40da-8a04-a7eb977365e7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart eq of normalised a7ba18fcd80f: P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart eq of normalised a7ba18
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart eq of normalised a7ba18fcd80f construction uses the P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart eq of normalised a7ba18fcd80f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsNormalise.lean#L56-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsNormalise.lean#L56-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsNormalise
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_eq_of_normalised_a7ba18fcd80f {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {j : ∀ k : FibreBlock κ, ι' k.1} {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    {z₁ z₂ : (Σ k', ι' k') → ℂ} (h₁v : ∀ p, z₁ (v p) = w p) (h₁j : ∀ k : FibreBlock κ, z₁ ⟨k.1, j k⟩ = 1)
    (h₂v : ∀ p, z₂ (v p) = w p) (h₂j : ∀ k : FibreBlock κ, z₂ ⟨k.1, j k⟩ = 1) (h : SameOrbit z₁ z₂) :
    z₁ = z₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«GenericPointsInAffineChart».«eq_of_normalised» := P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_eq_of_normalised_a7ba18fcd80f
