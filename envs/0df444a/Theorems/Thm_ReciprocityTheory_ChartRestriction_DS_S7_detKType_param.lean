-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_detKType_param
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.detKType_param
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:59.840542+00:00
-- url     : https://prove2.me/theorems/73a862ec-83aa-4070-91be-0e67e25d9379
-- title:
--   S7: det KType param
-- statement:
--   The S7 construction uses the det KType param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean#L264-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SmulOneMemUnitary.lean#L264-L324

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.detKType_param (p q : ℕ) (a b : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    lowK (epsHol p q) (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) = detWt p q a b ∧
      ((p : ℝ) + q - 1 < (a : ℝ) - b →
        IsHCParam (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) ∧
        GapAtLeast (epsHol p q) (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q))
          ((a : ℝ) - b - (p + q) + 1) ∧
        1 ≤ q0 (epsHol p q)) := by sorry
