-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCF_mem_inertia_map_iff
-- name    : ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:03.389884+00:00
-- url     : https://prove2.me/theorems/9e5ce505-505a-53d9-877a-f11188d840ff
-- title:
--   HCF: mem inertia map iff
-- statement:
--   The HCF construction uses the mem inertia map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean#L75-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HilbertClassFieldA.lean#L75-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCF
variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

theorem ReciprocityTheory.Neutral.Bridge.HCF.mem_inertia_map_iff (A : ValuationSubring L) (g : L ≃ₐ[K] L) :
    g ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      g • A = A ∧ ∀ x ∈ A, g x - x ∈ A.nonunits := by sorry
