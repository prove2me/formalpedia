-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_toFun_1ac65f6dd72f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_toFun_1ac65f6dd72f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:33.515357+00:00
-- url     : https://prove2.me/theorems/47f9f1d2-e3a2-4bcd-a980-5e477a4b77c9
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv to Fun 1ac65f6dd72f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv t
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv to Fun 1ac65f6dd72f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv to Fun 1ac65f6dd72f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/OneBlockIdealEqComapProjIdeal.lean#L64-L67

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_toFun_1ac65f6dd72f {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a) :
    funFieldEquiv P e.toFun = sectionVal e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«funFieldEquiv_toFun» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_toFun_1ac65f6dd72f
