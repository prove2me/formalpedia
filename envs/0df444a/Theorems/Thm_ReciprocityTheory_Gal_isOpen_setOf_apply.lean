-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isOpen_setOf_apply
-- name    : ReciprocityTheory.Gal.isOpen_setOf_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:54.586407+00:00
-- url     : https://prove2.me/theorems/2f315fd5-31ec-4acf-8fce-8e24c819cdd2
-- title:
--   Gal: is Open set Of apply
-- statement:
--   The Gal construction uses the is Open set Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L13-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]

theorem ReciprocityTheory.Gal.isOpen_setOf_apply (x : Ω) (P : Ω → Prop) : IsOpen {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by sorry
