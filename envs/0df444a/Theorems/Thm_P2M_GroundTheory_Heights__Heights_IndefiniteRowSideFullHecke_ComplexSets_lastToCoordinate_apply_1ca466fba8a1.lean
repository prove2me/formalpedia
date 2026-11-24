-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_apply_1ca466fba8a1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_apply_1ca466fba8a1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:55.604574+00:00
-- url     : https://prove2.me/theorems/468e1501-0a2c-4afb-9165-f81e98dae0bb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets last To Coordinate apply 1ca466fba8a1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets l
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets last To Coordinate apply 1ca466fba8a1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets last To Coordinate apply 1ca466fba8a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassDivisionAtPoint.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassDivisionAtPoint.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassDivisionAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassDivisionAtPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
variable {τ : Type} [DecidableEq τ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_apply_1ca466fba8a1 (c : τ) (w : Option {c' // c' ≠ c} → ℂ) (c' : τ) :
    lastToCoordinate c w c' = if h : c' = c then w none else w (some ⟨c', h⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«lastToCoordinate_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_lastToCoordinate_apply_1ca466fba8a1
