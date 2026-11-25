-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_alg
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_alg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:11.963059+00:00
-- url     : https://prove2.me/theorems/7a74d786-8980-44f7-909b-b9cac4489f29
-- title:
--   I: evl alg
-- statement:
--   The I construction uses the evl alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L204-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L204-L233

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.evl_alg (c ee S Q p1 p2 b1 b2 l : ℝ) (hc : 0 < c) (hee : 0 < ee) (hS : 0 ≤ S)
    (hQ : 0 ≤ Q) (hCS : p1 ^ 2 + p2 ^ 2 ≤ S * Q) :
    c ^ 2 * ee ^ 2 * ((p1 - S * b1) ^ 2 + (p2 - S * b2) ^ 2) ≤
        c * (S * ee) * (c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) -
          2 * ee * (p1 * b1 + p2 * b2)) + c * (S * ee) * l) ∧
      0 ≤ c * (Q * ee + S * (ee * (b1 ^ 2 + b2 ^ 2 - l)) - 2 * ee * (p1 * b1 + p2 * b2)) +
        c * (S * ee) * l := by sorry
