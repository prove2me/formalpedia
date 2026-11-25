-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_skodaOps
-- name    : ReciprocityTheory.L2DbarEstimates.H.skodaOps
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:49.324348+00:00
-- url     : https://prove2.me/theorems/0dbbbf89-53e4-520b-83ce-7d5f2b1ab7cb
-- title:
--   H: skoda Ops
-- statement:
--   The H construction uses the skoda Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SkodaOps.lean#L105-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SkodaOps.lean#L105-L255

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open scoped ENNReal InnerProductSpace

theorem ReciprocityTheory.L2DbarEstimates.H.skodaOps (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    SkodaOpsStatement n M := by sorry
