-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_exists_den
-- name    : ReciprocityTheory.Gal.exists_den
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:49.639537+00:00
-- url     : https://prove2.me/theorems/24a284ef-183b-44d1-b529-658648193e0d
-- title:
--   Gal: exists den
-- statement:
--   The Gal construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L25-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L25-L84

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]

theorem ReciprocityTheory.Gal.exists_den (F : Type*) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) {x : Ω} (hx : A.valuation x ≤ 1) :
    ∃ s t : Ω, IsIntegral ℤ s ∧ IsIntegral ℤ t ∧ A.valuation s = 1 ∧ s * x = t := by sorry
