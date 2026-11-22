-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
-- name    : ReciprocityTheory.Gal.continuousSMul_intCl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:23.382801+00:00
-- url     : https://prove2.me/theorems/321795ed-3cc6-45cc-8d0a-63b847c019eb
-- title:
--   Gal: continuous SMul int Cl
-- statement:
--   The Gal construction uses the continuous SMul int Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L190-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L190-L204

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
variable (F Ω)

theorem ReciprocityTheory.Gal.continuousSMul_intCl :
    @ContinuousSMul (Ω ≃ₐ[F] Ω) (IntCl F Ω) _ _ ⊥ := by sorry
