-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_evalAt_genPt_cfdf05393d79
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_evalAt_genPt_cfdf05393d79
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:00.598944+00:00
-- url     : https://prove2.me/theorems/77fd6ab3-0d57-4ab9-8040-d829077213eb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval At gen Pt cfdf05393d79: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval At gen Pt cfdf05393d
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval At gen Pt cfdf05393d79 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval At gen Pt cfdf05393d79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean#L25-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_evalAt_genPt_cfdf05393d79 (P : Ideal (MRing ι)) (f : MRing ι) : evalAt (genPt P) f = toFn P f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«evalAt_genPt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_evalAt_genPt_cfdf05393d79
