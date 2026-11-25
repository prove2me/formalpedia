-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_exists_normalise_ef1588a2430b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_exists_normalise_ef1588a2430b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:52:53.87725+00:00
-- url     : https://prove2.me/theorems/1e0d55c1-894f-4e31-8c0f-def4d69d0af2
-- title:
--   P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart exists normalise ef1588a2430b: P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart exists normalise ef1588
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart exists normalise ef1588a2430b construction uses the P2 M Ground Theory Heights  Heights Inter Generic Points In Affine Chart exists normalise ef1588a2430b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsNormalise.lean#L24-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsNormalise.lean#L24-L52

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
omit [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_exists_normalise_ef1588a2430b {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} (hP' : IsMultiHomogIdeal P') {j : ∀ k : FibreBlock κ, ι' k.1}
    {z : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P')
    (hzz : SameOrbit (fun p => z' (v p)) z) (hj : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) :
    ∃ d : K' → ℂ, (∀ k, d k ≠ 0) ∧ (fun q => d q.1 * z' q) ∈ mcPts P' ∧
      (∀ p, d (v p).1 * z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, d k.1 * z' ⟨k.1, j k⟩ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«GenericPointsInAffineChart».«exists_normalise» := P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_exists_normalise_ef1588a2430b
