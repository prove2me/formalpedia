-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_isRoot_map_eval_c7fa46924b2e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_isRoot_map_eval_c7fa46924b2e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:26:27.5228+00:00
-- url     : https://prove2.me/theorems/4d4d4812-53ad-4f2f-8855-bc7211ece8e9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets norm lt of is Root map eval c7fa46924b2e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Set
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets norm lt of is Root map eval c7fa46924b2e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets norm lt of is Root map eval c7fa46924b2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelProper.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalModelProper.lean#L25-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_isRoot_map_eval_c7fa46924b2e {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hPm : P.Monic)
    (x : Fin n → ℂ) {a : ℂ} (ha : (P.map (eval x)).IsRoot a) :
    ‖a‖ < 1 + ∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«norm_lt_of_isRoot_map_eval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_isRoot_map_eval_c7fa46924b2e
