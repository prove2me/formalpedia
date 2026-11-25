-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ap
-- name    : ReciprocityTheory.L2DbarEstimates.E.ap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:41.983024+00:00
-- url     : https://prove2.me/theorems/d3233302-abcd-5c68-9b23-237bfe168369
-- title:
--   E: ap
-- statement:
--   The E construction uses the ap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/Imports.lean#L15-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/Imports.lean#L15-L136

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportOfVanish
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_TstarNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_Imports
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
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.E.ap (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : APStatement n M := by sorry
