-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_real_smul_mem_coneSet_09cb40c5598f
-- name    : P2M_GroundTheory_Heights__Heights_real_smul_mem_coneSet_09cb40c5598f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:58.382011+00:00
-- url     : https://prove2.me/theorems/b972f24b-10cb-44dc-8173-fa2fd9fa73ad
-- title:
--   P2 M Ground Theory Heights  Heights real smul mem cone Set 09cb40c5598f: P2 M Ground Theory Heights  Heights real smul mem cone Set 09cb40c5598f
-- statement:
--   The P2 M Ground Theory Heights  Heights real smul mem cone Set 09cb40c5598f construction uses the P2 M Ground Theory Heights  Heights real smul mem cone Set 09cb40c5598f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeFibreAverage.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFibreAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_real_smul_mem_coneSet_09cb40c5598f {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) (t : ℝ) :
    t • y ∈ coneSet h J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«real_smul_mem_coneSet» := P2M_GroundTheory_Heights__Heights_real_smul_mem_coneSet_09cb40c5598f
