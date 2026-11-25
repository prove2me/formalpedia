-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreBlock_inl_subsingleton_2ebb000443cf
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreBlock_inl_subsingleton_2ebb000443cf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:45.68617+00:00
-- url     : https://prove2.me/theorems/04aa1368-8ef2-4894-aa19-097eec2db892
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Block inl subsingleton 2ebb000443cf: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Block
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Block inl subsingleton 2ebb000443cf construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Block inl subsingleton 2ebb000443cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L150-L155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreBlock_inl_subsingleton_2ebb000443cf (k k' : FibreBlock (Sum.inl : K → K ⊕ Unit)) : k = k' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«fibreBlock_inl_subsingleton» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreBlock_inl_subsingleton_2ebb000443cf
