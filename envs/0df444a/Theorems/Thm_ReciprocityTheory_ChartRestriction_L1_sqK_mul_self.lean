-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqK_mul_self
-- name    : ReciprocityTheory.ChartRestriction.L1.sqK_mul_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:47:15.082317+00:00
-- url     : https://prove2.me/theorems/bf92ff83-b6a5-4ef0-be3b-3c8e22adcbdf
-- title:
--   L1: sq K mul self
-- statement:
--   The L1 construction uses the sq K mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModPrincNorm.lean#L42-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.sqK_mul_self (d : ℕ) : sqK d * sqK d = -(d : KQ d) := by sorry
