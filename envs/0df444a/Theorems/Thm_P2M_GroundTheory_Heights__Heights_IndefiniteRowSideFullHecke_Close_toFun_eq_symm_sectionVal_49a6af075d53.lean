-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_toFun_eq_symm_sectionVal_49a6af075d53
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_toFun_eq_symm_sectionVal_49a6af075d53
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:03.149835+00:00
-- url     : https://prove2.me/theorems/6cb37c95-9409-509a-a3a7-1ad7a409dce9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close to Fun eq symm section Val 49a6af075d53: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close to Fun eq sym
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close to Fun eq symm section Val 49a6af075d53 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close to Fun eq symm section Val 49a6af075d53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L69-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_toFun_eq_symm_sectionVal_49a6af075d53 {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) :
    e.toFun = (funFieldEquiv P).symm (sectionVal e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«toFun_eq_symm_sectionVal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_toFun_eq_symm_sectionVal_49a6af075d53
