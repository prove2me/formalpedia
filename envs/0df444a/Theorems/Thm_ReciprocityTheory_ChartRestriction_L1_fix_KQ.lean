-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_fix_KQ
-- name    : ReciprocityTheory.ChartRestriction.L1.fix_KQ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:50.595271+00:00
-- url     : https://prove2.me/theorems/51f46233-6617-469e-a878-7f82d7f4be49
-- title:
--   L1: fix KQ
-- statement:
--   The L1 construction uses the fix KQ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocD.lean#L72-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModLocD.lean#L72-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane Pointwise
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.fix_KQ {d l : ℕ} [Fact l.Prime] (e : Om d →+* PadicAlgCl l)
    (ρ : PadicAlgCl l ≃ₐ[IntermediateField.adjoin ℚ_[l] {e (algebraMap (KQ d) (Om d) (sqK d))}] PadicAlgCl l)
    (k : KQ d) : ρ (e (algebraMap (KQ d) (Om d) k)) = e (algebraMap (KQ d) (Om d) k) := by sorry
