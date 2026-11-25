-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_comap_eq_maximalIdeal_e63e4b11dba8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_comap_eq_maximalIdeal_e63e4b11dba8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:17.129498+00:00
-- url     : https://prove2.me/theorems/cc037e66-4b48-4f62-b799-31da9bac38a6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart comap eq maximal Ideal e63e4b11dba8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blo
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart comap eq maximal Ideal e63e4b11dba8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Blow Up Chart comap eq maximal Ideal e63e4b11dba8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ComapEqMaximalIdeal.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ComapEqMaximalIdeal.lean#L12-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ComapEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_comap_eq_maximalIdeal_e63e4b11dba8 {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {n : ℕ} {x : Fin n → A}
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A) {i : Fin n} (hi : x i ≠ 0)
    (P : Ideal (blowUpChart A K x i)) (hP : P.IsPrime) (hxP : algebraMap A _ (x i) ∈ P) :
    P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«BlowUpChart».«comap_eq_maximalIdeal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BlowUpChart_comap_eq_maximalIdeal_e63e4b11dba8
