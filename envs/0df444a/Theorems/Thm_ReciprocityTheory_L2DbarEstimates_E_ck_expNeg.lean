-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_expNeg
-- name    : ReciprocityTheory.L2DbarEstimates.E.ck_expNeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:27.935798+00:00
-- url     : https://prove2.me/theorems/7ebeabeb-6ad0-4d14-bd29-9d9df1f1e213
-- title:
--   E: ck exp Neg
-- statement:
--   The E construction uses the ck exp Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L11-L17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.E.ck_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (hph : CkR n z k ph) :
    Ck n z k (fun x => (Real.exp (-ph x) : ℂ)) := by sorry
