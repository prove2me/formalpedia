-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_vecEmpty_eq_elim0_909cf59b659a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_vecEmpty_eq_elim0_909cf59b659a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:36.622171+00:00
-- url     : https://prove2.me/theorems/0b2e5e98-106f-46c2-91fd-eeec3057273c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter vec Empty eq elim0 909cf59b659a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter vec Empty eq elim0 90
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter vec Empty eq elim0 909cf59b659a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter vec Empty eq elim0 909cf59b659a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/MultAtHorizontalEqZero.lean#L28-L28

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_vecEmpty_eq_elim0_909cf59b659a : (![] : Fin 0 → HermLine ι) = Fin.elim0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«vecEmpty_eq_elim0» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_vecEmpty_eq_elim0_909cf59b659a
