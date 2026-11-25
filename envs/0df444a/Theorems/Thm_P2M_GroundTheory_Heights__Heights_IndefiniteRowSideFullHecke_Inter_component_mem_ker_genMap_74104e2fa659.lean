-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_component_mem_ker_genMap_74104e2fa659
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_component_mem_ker_genMap_74104e2fa659
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:49.554963+00:00
-- url     : https://prove2.me/theorems/27a5b6c7-804c-4342-9e54-0ffb3d9d92bf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter component mem ker gen Map 74104e2fa659: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter component mem
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter component mem ker gen Map 74104e2fa659 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter component mem ker gen Map 74104e2fa659 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L137-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L137-L163

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_component_mem_ker_genMap_74104e2fa659 [DecidableEq K] (P : Ideal (MRing ι)) (G : Set (MRing ι))
    (hG : ∀ f ∈ G, ∃ a, IsMultiHomog f a) (hPG : P = Ideal.span G) {N1 : ℕ}
    (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ)
    (hV : ∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s))
    {f : MRing (PBlk ι N1)} (hf : f ∈ RingHom.ker (genMap P fun s j => toFn P (V s j)))
    (b : K ⊕ Unit → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (PBlk ι N1)) b f ∈
      RingHom.ker (genMap P fun s j => toFn P (V s j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«component_mem_ker_genMap» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_component_mem_ker_genMap_74104e2fa659
