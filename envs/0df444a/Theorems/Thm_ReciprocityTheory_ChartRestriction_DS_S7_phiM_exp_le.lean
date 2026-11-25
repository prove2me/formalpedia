-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_exp_le
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.phiM_exp_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:51.377616+00:00
-- url     : https://prove2.me/theorems/1a699ee6-1211-5478-a2f9-38ee81322bf5
-- title:
--   S7: phi M exp le
-- statement:
--   The S7 construction uses the phi M exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiDecayCore.lean#L131-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/PhiDecayCore.lean#L131-L184

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiDecayCore
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
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.phiM_exp_le (μ : Fin n → ℤ) (hμ : IsMu lam μ) (hlam : IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    (PhiM μ (NormedSpace.exp Y)).re ≤
      Real.exp (-(h / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε))) := by sorry
