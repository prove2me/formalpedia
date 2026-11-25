-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sepInt
-- name    : ReciprocityTheory.ChartRestriction.L1.sepInt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:03.448807+00:00
-- url     : https://prove2.me/theorems/a29f4c50-1f6b-46e3-91a2-f3d7177d01ca
-- title:
--   L1: sep Int
-- statement:
--   The L1 construction uses the sep Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModSepInt.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModSepInt.lean#L35-L55

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

theorem ReciprocityTheory.ChartRestriction.L1.sepInt {Ω : Type*} [Field Ω] [CharZero Ω] (s : Finset Ω) (hs : ∀ r ∈ s, IsIntegral ℤ r) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ A : ValuationSubring Ω, r - r' ∈ A.nonunits →
      (n : Ω) ∈ A.nonunits := by sorry
