-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casValK_add
-- name    : ReciprocityTheory.ChartRestriction.DS.casValK_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:20.852008+00:00
-- url     : https://prove2.me/theorems/01ef7cd9-2267-487e-aec3-a78e3cc2652f
-- title:
--   DS: cas Val K add
-- statement:
--   The DS construction uses the cas Val K add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L185-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/NumRho.lean#L185-L189

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
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

theorem ReciprocityTheory.ChartRestriction.DS.casValK_add (μ ν : Fin n → ℝ) :
    casValK ε (μ + ν) = casValK ε μ + 2 * dot (μ + rhoC ε) ν + nsq ν := by sorry
