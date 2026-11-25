-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_div_mul_pow_4b1d77712065
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_div_mul_pow_4b1d77712065
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:47.822553+00:00
-- url     : https://prove2.me/theorems/0912665e-3589-563c-afbf-7b270db6d124
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic eval div mul pow 4b1d77712065: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mon
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic eval div mul pow 4b1d77712065 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic eval div mul pow 4b1d77712065 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalBoundedQuotient.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalBoundedQuotient.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalBoundedQuotient
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
open MvPolynomial Topology

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_div_mul_pow_4b1d77712065 {d : ℕ} (a : Fin d → ℂ) {F G : ℂ} (hG : G ≠ 0) :
    F ^ d + ∑ j : Fin d, a j * F ^ (j : ℕ) * G ^ (d - (j : ℕ)) =
      G ^ d * ((F / G) ^ d + ∑ j : Fin d, a j * (F / G) ^ (j : ℕ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«monic_eval_div_mul_pow» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_eval_div_mul_pow_4b1d77712065
