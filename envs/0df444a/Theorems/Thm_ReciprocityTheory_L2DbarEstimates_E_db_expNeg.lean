-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_db_expNeg
-- name    : ReciprocityTheory.L2DbarEstimates.E.db_expNeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:02:57.961748+00:00
-- url     : https://prove2.me/theorems/1d91076d-241c-5055-99b6-31864c9f4ea7
-- title:
--   E: db exp Neg
-- statement:
--   The E construction uses the db exp Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L26-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L26-L55

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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

theorem ReciprocityTheory.L2DbarEstimates.E.db_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n)
    (x : M) :
    db n z j (fun y => (Real.exp (-ph y) : ℂ)) x =
      -((Real.exp (-ph x) : ℂ) * db n z j (fun y => (ph y : ℂ)) x) := by sorry
