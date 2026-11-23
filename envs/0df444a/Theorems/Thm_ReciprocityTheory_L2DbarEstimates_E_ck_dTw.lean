-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_dTw
-- name    : ReciprocityTheory.L2DbarEstimates.E.ck_dTw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:23.036565+00:00
-- url     : https://prove2.me/theorems/508b3cda-510a-445e-b9bb-f8d65a6c85f9
-- title:
--   E: ck d Tw
-- statement:
--   The E construction uses the ck d Tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L97-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L97-L112

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

theorem ReciprocityTheory.L2DbarEstimates.E.ck_dTw {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (ph : M → ℝ) (j : Fin n) (u : M → ℂ)
    (hph : CkR n z (k + 1) ph) (hu : Ck n z (k + 1) u) : Ck n z k (dTw n z ph j u) := by sorry
