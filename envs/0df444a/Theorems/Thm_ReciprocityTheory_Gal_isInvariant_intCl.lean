-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl
-- name    : ReciprocityTheory.Gal.isInvariant_intCl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:20.504812+00:00
-- url     : https://prove2.me/theorems/108f5639-0fe9-49ee-9d4a-8b30e58bc1c4
-- title:
--   Gal: is Invariant int Cl
-- statement:
--   The Gal construction uses the is Invariant int Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L208-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalB.lean#L208-L220

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

theorem ReciprocityTheory.Gal.isInvariant_intCl : Algebra.IsInvariant (𝓞 F) (IntCl F Ω) (Ω ≃ₐ[F] Ω) := by sorry
