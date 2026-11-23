-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_contDiffAt_phiP
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.Ps1.contDiffAt_phiP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:34.123533+00:00
-- url     : https://prove2.me/theorems/a52770c7-8d67-4248-b009-e58299c13ea8
-- title:
--   Ps1: cont Diff At phi P
-- statement:
--   The Ps1 construction uses the cont Diff At phi P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/ContinuousOnFderivPhiP.lean#L49-L52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
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
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ

theorem ReciprocityTheory.ChartRestriction.DS.S7.Ps1.contDiffAt_phiP (μ : Fin n → ℤ) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    ContDiffAt ℂ 1 (PhiP μ) z := by sorry
