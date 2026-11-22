-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isClosed_setOf_apply
-- name    : ReciprocityTheory.Gal.isClosed_setOf_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:21.471649+00:00
-- url     : https://prove2.me/theorems/69b67809-d6c4-4212-b620-5fc30c0f7f91
-- title:
--   Gal: is Closed set Of apply
-- statement:
--   The Gal construction uses the is Closed set Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalA.lean#L39-L41

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

theorem ReciprocityTheory.Gal.isClosed_setOf_apply (x : Ω) (P : Ω → Prop) : IsClosed {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by sorry
