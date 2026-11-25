-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_isSectionOn_5e773a81802a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_isSectionOn_5e773a81802a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:28.409211+00:00
-- url     : https://prove2.me/theorems/0f2da6c8-460e-40c2-82cb-a19495bc6b6a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff is Section On 5e773a81802a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff is S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff is Section On 5e773a81802a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter is Sec iff is Section On 5e773a81802a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L18-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_isSectionOn_5e773a81802a (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ IsSectionOn P A s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«isSec_iff_isSectionOn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_isSectionOn_5e773a81802a
