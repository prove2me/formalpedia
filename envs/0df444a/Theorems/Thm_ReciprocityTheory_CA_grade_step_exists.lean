-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_grade_step_exists
-- name    : ReciprocityTheory.CA.grade_step_exists
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:44.729367+00:00
-- url     : https://prove2.me/theorems/96fa4c21-593e-4c86-97ad-fc33813bd053
-- title:
--   CA: grade step exists
-- statement:
--   The CA construction uses the grade step exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularOfLeHeight.lean#L24-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ExistsIsRegularOfLeHeight.lean#L24-L52

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

theorem ReciprocityTheory.CA.grade_step_exists (h : IsCM R) {I : Ideal R} (hI : I ≠ ⊤) {r : ℕ}
    (hr : (r : ℕ∞) ≤ I.height) (rs : List R) (hlen : rs.length < r) (hrsI : ∀ x ∈ rs, x ∈ I)
    (reg : IsRegular R rs) :
    ∃ x ∈ I, IsSMulRegular (R ⧸ (Ideal.ofList rs • ⊤ : Submodule R R)) x := by sorry
