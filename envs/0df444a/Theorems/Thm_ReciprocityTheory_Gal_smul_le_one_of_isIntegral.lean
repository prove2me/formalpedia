-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_smul_le_one_of_isIntegral
-- name    : ReciprocityTheory.Gal.smul_le_one_of_isIntegral
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:38.929479+00:00
-- url     : https://prove2.me/theorems/2ab33736-11b9-43eb-b7aa-e8206d0dbbc6
-- title:
--   Gal: smul le one of is Integral
-- statement:
--   The Gal construction uses the smul le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L122-L125

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
omit [NumberField F] [IsAlgClosure F Ω]

theorem ReciprocityTheory.Gal.smul_le_one_of_isIntegral (g : Ω ≃ₐ[F] Ω) {A : ValuationSubring Ω}
    (hA : ∀ b : Ω, IsIntegral ℤ b → b ∈ A) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ g • A := by sorry
