-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermValue_polyGerm_02f2c54c1f02
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermValue_polyGerm_02f2c54c1f02
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:39.491805+00:00
-- url     : https://prove2.me/theorems/3514dbc8-d721-4487-af1a-e33810c21e4c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hol Germ Value poly Germ 02f2c54c1f02: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets h
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hol Germ Value poly Germ 02f2c54c1f02 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hol Germ Value poly Germ 02f2c54c1f02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StZariskiObjects.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StZariskiObjects.lean#L25-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
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
open MvPolynomial Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermValue_polyGerm_02f2c54c1f02 {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    holGermValue w (polyGerm w q) = eval w q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«holGermValue_polyGerm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_holGermValue_polyGerm_02f2c54c1f02
