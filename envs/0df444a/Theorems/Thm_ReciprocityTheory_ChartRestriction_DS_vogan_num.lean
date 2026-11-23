-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_vogan_num
-- name    : ReciprocityTheory.ChartRestriction.DS.vogan_num
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:21.250372+00:00
-- url     : https://prove2.me/theorems/d0c331fb-ccae-4c14-81a5-cca6dcfa5995
-- title:
--   DS: vogan num
-- statement:
--   The DS construction uses the vogan num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L142-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L142-L164

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.vogan_num {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by sorry
