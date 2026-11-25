-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericSubstitution_isWeightedHomogeneous_61102d448a34
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericSubstitution_isWeightedHomogeneous_61102d448a34
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:38.590712+00:00
-- url     : https://prove2.me/theorems/f9b70b72-4048-4606-9f2a-f916f8242098
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Substitution is Weighted Homogeneous 61102d448a34: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke I
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Substitution is Weighted Homogeneous 61102d448a34 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter generic Substitution is Weighted Homogeneous 61102d448a34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L46-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L46-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (ι) {S : Type} [Fintype S] (γ : S → K → ℕ)
variable {ι} {N1 : ℕ}
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericSubstitution_isWeightedHomogeneous_61102d448a34 (V : S → Fin N1 → MRing ι)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    (v : Σ x, PBlk ι N1 x) :
    IsWeightedHomogeneous (genericWeight ι γ) (genericSubstitution V v) (zDeg (NumbersDVR.blockWeight (PBlk ι N1) v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«genericSubstitution_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericSubstitution_isWeightedHomogeneous_61102d448a34
