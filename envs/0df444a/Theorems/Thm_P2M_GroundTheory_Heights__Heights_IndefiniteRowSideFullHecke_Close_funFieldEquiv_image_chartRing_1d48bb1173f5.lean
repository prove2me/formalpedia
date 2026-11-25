-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_image_chartRing_1d48bb1173f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_image_chartRing_1d48bb1173f5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:41.356734+00:00
-- url     : https://prove2.me/theorems/1470c858-0be9-4a2d-a8ed-40cf5a73b6a2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv image chart Ring 1d48bb1173f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Fie
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv image chart Ring 1d48bb1173f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close fun Field Equiv image chart Ring 1d48bb1173f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/FunFieldEquivMemChartRingIff.lean#L43-L54

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_image_chartRing_1d48bb1173f5 (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) :
    funFieldEquiv P '' (P.chartRing c : Set P.FunField) = (chartRing P c : Set (FunField P)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«funFieldEquiv_image_chartRing» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_funFieldEquiv_image_chartRing_1d48bb1173f5
