-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_valuationSubring_of_isIntegral
-- name    : ReciprocityTheory.ChartRestriction.L1.mem_valuationSubring_of_isIntegral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:14.205652+00:00
-- url     : https://prove2.me/theorems/44299fef-bcd9-4755-8e87-d4187bf5b9b1
-- title:
--   L1: mem valuation Subring of is Integral
-- statement:
--   The L1 construction uses the mem valuation Subring of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModSepInt.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModSepInt.lean#L28-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
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

theorem ReciprocityTheory.ChartRestriction.L1.mem_valuationSubring_of_isIntegral {Ω : Type*} [Field Ω] {x : Ω} (hx : IsIntegral ℤ x)
    (A : ValuationSubring Ω) : x ∈ A := by sorry
