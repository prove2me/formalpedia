-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_lt_one_iff
-- name    : ReciprocityTheory.Gal.smul_valuation_lt_one_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:35.018177+00:00
-- url     : https://prove2.me/theorems/639cb916-b9c7-49ee-93b8-f2307fe7ba2f
-- title:
--   Gal: smul valuation lt one iff
-- statement:
--   The Gal construction uses the smul valuation lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L114-L119

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
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem ReciprocityTheory.Gal.smul_valuation_lt_one_iff (g : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Ω ≃ₐ[F] Ω) y) < 1 := by sorry
