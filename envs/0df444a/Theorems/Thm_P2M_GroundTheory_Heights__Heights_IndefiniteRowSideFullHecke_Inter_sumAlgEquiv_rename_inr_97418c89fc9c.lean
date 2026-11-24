-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sumAlgEquiv_rename_inr_97418c89fc9c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sumAlgEquiv_rename_inr_97418c89fc9c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:14.506369+00:00
-- url     : https://prove2.me/theorems/e104b55e-1d70-43b3-949e-3670bc02ebc5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum Alg Equiv rename inr 97418c89fc9c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum Alg Equiv r
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum Alg Equiv rename inr 97418c89fc9c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter sum Alg Equiv rename inr 97418c89fc9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomog.lean#L83-L86

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
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sumAlgEquiv_rename_inr_97418c89fc9c (f : MRing ι) :
    sumAlgEquiv ℤ S (Σ k, ι k) (rename Sum.inr f) = C f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«sumAlgEquiv_rename_inr» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sumAlgEquiv_rename_inr_97418c89fc9c
