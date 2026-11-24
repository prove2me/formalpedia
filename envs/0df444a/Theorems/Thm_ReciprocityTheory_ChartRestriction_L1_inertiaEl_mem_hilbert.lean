-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inertiaEl_mem_hilbert
-- name    : ReciprocityTheory.ChartRestriction.L1.inertiaEl_mem_hilbert
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:32.902308+00:00
-- url     : https://prove2.me/theorems/94976c35-9376-425d-b85a-c6ba7b73e51a
-- title:
--   L1: inertia El mem hilbert
-- statement:
--   The L1 construction uses the inertia El mem hilbert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L73-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
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

theorem ReciprocityTheory.ChartRestriction.L1.inertiaEl_mem_hilbert {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {g : Ω ≃ₐ[E] Ω} (h : InertiaEl A g) : g ∈ hilbertSubgroup E Ω := by sorry
