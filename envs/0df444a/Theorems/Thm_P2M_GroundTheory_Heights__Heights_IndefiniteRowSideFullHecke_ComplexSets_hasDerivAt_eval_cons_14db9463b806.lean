-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasDerivAt_eval_cons_14db9463b806
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasDerivAt_eval_cons_14db9463b806
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:48.024647+00:00
-- url     : https://prove2.me/theorems/d571e9d4-4e7e-482e-b105-afb5d8a4464a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets has Deriv At eval cons 14db9463b806: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets has
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets has Deriv At eval cons 14db9463b806 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets has Deriv At eval cons 14db9463b806 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PContinuousRootHolomorphic.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PContinuousRootHolomorphic.lean#L10-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StContinuousRootHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PContinuousRootHolomorphic
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
open MvPolynomial Filter
open scoped Topology

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasDerivAt_eval_cons_14db9463b806 {k : ℕ} (y : Fin k → ℂ) (P : MvPolynomial (Fin (k + 1)) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => eval (Fin.cons s y : Fin (k + 1) → ℂ) P)
      (eval (Fin.cons s y : Fin (k + 1) → ℂ) (pderiv 0 P)) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«hasDerivAt_eval_cons» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hasDerivAt_eval_cons_14db9463b806
