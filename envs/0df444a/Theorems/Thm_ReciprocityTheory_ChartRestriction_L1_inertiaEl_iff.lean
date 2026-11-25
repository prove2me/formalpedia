-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inertiaEl_iff
-- name    : ReciprocityTheory.ChartRestriction.L1.inertiaEl_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:35.361381+00:00
-- url     : https://prove2.me/theorems/814669d6-6b78-4fff-861f-ce6bf078fdcc
-- title:
--   L1: inertia El iff
-- statement:
--   The L1 construction uses the inertia El iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L45-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModGBasic.lean#L45-L71

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

theorem ReciprocityTheory.ChartRestriction.L1.inertiaEl_iff {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) :
    InertiaEl A g ↔ g ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype := by sorry
