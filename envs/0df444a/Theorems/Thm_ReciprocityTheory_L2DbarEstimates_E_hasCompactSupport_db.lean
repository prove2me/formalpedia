-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_hasCompactSupport_db
-- name    : ReciprocityTheory.L2DbarEstimates.E.hasCompactSupport_db
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:05.681921+00:00
-- url     : https://prove2.me/theorems/85e8279b-c4a4-46c0-97f5-777bf6c13b52
-- title:
--   E: has Compact Support db
-- statement:
--   The E construction uses the has Compact Support db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportDTw.lean#L172-L176

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

theorem ReciprocityTheory.L2DbarEstimates.E.hasCompactSupport_db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (u : M → ℂ)
    (hu : HasCompactSupport u) : HasCompactSupport (db n z j u) := by sorry
