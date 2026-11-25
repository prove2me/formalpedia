-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genMap_eq_comp_d39810b8d8dc
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genMap_eq_comp_d39810b8d8dc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:36.404216+00:00
-- url     : https://prove2.me/theorems/aeb10f5d-d158-4022-8a0c-7a1c970f4636
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter gen Map eq comp d39810b8d8dc: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter gen Map eq comp d39810b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter gen Map eq comp d39810b8d8dc construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter gen Map eq comp d39810b8d8dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L95-L104

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genMap_eq_comp_d39810b8d8dc [DecidableEq K] (P : Ideal (MRing ι)) {N1 : ℕ} (V : S → Fin N1 → MRing ι) :
    genMap P (fun s j => toFn P (V s j)) = (genericEvaluation P).comp (aeval (genericSubstitution V)).toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«genMap_eq_comp» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genMap_eq_comp_d39810b8d8dc
