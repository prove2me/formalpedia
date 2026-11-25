-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
-- name    : ReciprocityTheory.Gal.eq_of_valuation_lt_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:43.163811+00:00
-- url     : https://prove2.me/theorems/27ac0eba-db09-4888-a97a-a9851aa5f1bd
-- title:
--   Gal: eq of valuation lt one iff
-- statement:
--   The Gal construction uses the eq of valuation lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L102-L106

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

theorem ReciprocityTheory.Gal.eq_of_valuation_lt_one_iff (F : Type*) [Field F] [NumberField F] [Algebra F Ω]
    [IsAlgClosure F Ω] {A A' : ValuationSubring Ω}
    (h : ∀ b : Ω, IsIntegral ℤ b → (A.valuation b < 1 ↔ A'.valuation b < 1)) : A = A' := by sorry
