-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isKerBasis_idRows_c47ff629142f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isKerBasis_idRows_c47ff629142f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:39.815998+00:00
-- url     : https://prove2.me/theorems/c1a21ca0-16da-4efa-83ac-5fbc3bb00615
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Ker Basis id Rows c47ff629142f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Ker Basis id Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Ker Basis id Rows c47ff629142f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Ker Basis id Rows c47ff629142f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L288-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ProjLineRankTwoPushforwardHypotheses.lean#L288-L293

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isKerBasis_idRows_c47ff629142f (n : ℕ) : IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows n) (idRows n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isKerBasis_idRows» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isKerBasis_idRows_c47ff629142f
