-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_hasCompactSupport_of_vanish
-- name    : ReciprocityTheory.L2DbarEstimates.E.hasCompactSupport_of_vanish
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:56:00.592818+00:00
-- url     : https://prove2.me/theorems/abeffea3-93f2-4655-9bc7-3fda0ffce855
-- title:
--   E: has Compact Support of vanish
-- statement:
--   The E construction uses the has Compact Support of vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportOfVanish.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportOfVanish.lean#L25-L27

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportOfVanish
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

theorem ReciprocityTheory.L2DbarEstimates.E.hasCompactSupport_of_vanish {M : Type*} [TopologicalSpace M] (u F : M → ℂ)
    (hu : HasCompactSupport u) (h : ∀ x, u x = 0 → F x = 0) : HasCompactSupport F := by sorry
