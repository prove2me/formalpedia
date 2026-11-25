-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_serreAt_of_isIntegrallyClosed_3a2a85072b20
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_serreAt_of_isIntegrallyClosed_3a2a85072b20
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:41.954854+00:00
-- url     : https://prove2.me/theorems/c65f06de-b162-497c-8da4-130179f635ea
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets serre At of is Integrally Closed 3a2a85072b20: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comple
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets serre At of is Integrally Closed 3a2a85072b20 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets serre At of is Integrally Closed 3a2a85072b20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatNormalFibres.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatNormalFibres.lean#L42-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreRFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
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
open IsLocalRing RingTheory.Sequence

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_serreAt_of_isIntegrallyClosed_3a2a85072b20 (hC : SerreCriterion.Statement) (B : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] : SerreRAt B 1 ∧ SerreSAt B 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«serreAt_of_isIntegrallyClosed» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_serreAt_of_isIntegrallyClosed_3a2a85072b20
