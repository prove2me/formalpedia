-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_exists_isRegular_of_le_height
-- name    : ReciprocityTheory.CA.IsCM.exists_isRegular_of_le_height
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:15.763377+00:00
-- url     : https://prove2.me/theorems/b1032574-835b-4848-8123-9d7b666da9c5
-- title:
--   Is CM: exists is Regular of le height
-- statement:
--   The Is CM construction uses the exists is Regular of le height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularOfLeHeight.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularOfLeHeight.lean#L66-L82

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_RingKrullDimQuotientOfMemAssociatedPrimes
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem ReciprocityTheory.CA.IsCM.exists_isRegular_of_le_height (h : IsCM R) {I : Ideal R} (hI : I ≠ ⊤) {r : ℕ}
    (hr : (r : ℕ∞) ≤ I.height) :
    ∃ rs : List R, rs.length = r ∧ (∀ x ∈ rs, x ∈ I) ∧ IsRegular R rs := by sorry
