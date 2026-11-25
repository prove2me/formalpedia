-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logLogStep_arith_994d7a824460
-- name    : P2M_GroundTheory_Heights__Heights_logLogStep_arith_994d7a824460
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:34.80333+00:00
-- url     : https://prove2.me/theorems/a3e9ea27-76fc-4b52-9152-3032a4b56624
-- title:
--   P2 M Ground Theory Heights  Heights log Log Step arith 994d7a824460: P2 M Ground Theory Heights  Heights log Log Step arith 994d7a824460
-- statement:
--   The P2 M Ground Theory Heights  Heights log Log Step arith 994d7a824460 construction uses the P2 M Ground Theory Heights  Heights log Log Step arith 994d7a824460 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessDeriv.lean#L45-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLogLogCutHessDeriv.lean#L45-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLogLogCutHessDeriv
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
open Filter Topology
open scoped ContDiff
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_logLogStep_arith_994d7a824460 {C c t p q f v w : ℝ} (hC0 : 0 ≤ C) (hc : 1 ≤ c) (ht : t ≠ 0) (hp : |p| ≤ C)
    (hq : |q| ≤ C) (hf : |f| ≤ 1) (hv : v = -(2 * (t⁻¹ / c))) (hw : w = -(2 * (-(t ^ 2)⁻¹ / c))) :
    |q * v * v + p * w| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) ∧
      |p * v * (p * v) + f * (q * v * v + p * w)| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logLogStep_arith» := P2M_GroundTheory_Heights__Heights_logLogStep_arith_994d7a824460
