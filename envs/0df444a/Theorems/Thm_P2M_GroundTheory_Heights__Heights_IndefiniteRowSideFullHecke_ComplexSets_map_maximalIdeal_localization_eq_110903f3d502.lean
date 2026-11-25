-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_map_maximalIdeal_localization_eq_110903f3d502
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_map_maximalIdeal_localization_eq_110903f3d502
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:25.864811+00:00
-- url     : https://prove2.me/theorems/e7f3bbb8-3193-4340-b73e-44f8540b23a9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets map maximal Ideal localization eq 110903f3d502: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Compl
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets map maximal Ideal localization eq 110903f3d502 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets map maximal Ideal localization eq 110903f3d502 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSerreRFlatAscentLocal.lean#L88-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
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
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_map_maximalIdeal_localization_eq_110903f3d502 :
    letI := Localization.AtPrime.algebraOfLiesOver (P.under A) P
    (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P))
        (Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«map_maximalIdeal_localization_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_map_maximalIdeal_localization_eq_110903f3d502
