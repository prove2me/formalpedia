-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_X_sub_C_mul_succ_64640c148516
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_X_sub_C_mul_succ_64640c148516
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:10.722123+00:00
-- url     : https://prove2.me/theorems/8d72780d-29bd-46d0-9de6-0838a8d41fa2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coeff X sub C mul succ 64640c148516: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coe
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coeff X sub C mul succ 64640c148516 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets coeff X sub C mul succ 64640c148516 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_X_sub_C_mul_succ_64640c148516 (a : ℂ) (q : Polynomial ℂ) (n : ℕ) :
    ((Polynomial.X - Polynomial.C a) * q).coeff (n + 1) = q.coeff n - a * q.coeff (n + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«coeff_X_sub_C_mul_succ» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_coeff_X_sub_C_mul_succ_64640c148516
