-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartPow_neg_7b7d27d152fb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartPow_neg_7b7d27d152fb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:21.611526+00:00
-- url     : https://prove2.me/theorems/efc42ae5-98ff-5c66-8e07-525ff0875ed3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Pow neg 7b7d27d152fb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Pow neg 7b7d27d152fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Pow neg 7b7d27d152fb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close chart Pow neg 7b7d27d152fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L69-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_FunFieldEquivMemChartRingIff
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartPow_neg_7b7d27d152fb (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (a : ι → ℤ) :
    chartPow P c (-a) = (chartPow P c a)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«chartPow_neg» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartPow_neg_7b7d27d152fb
