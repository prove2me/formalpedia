-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isMaximal_span_prime
-- name    : ReciprocityTheory.Gal.isMaximal_span_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:54.970601+00:00
-- url     : https://prove2.me/theorems/f0f117c4-9f5f-4616-9f1f-086cc23c5ce1
-- title:
--   Gal: is Maximal span prime
-- statement:
--   The Gal construction uses the is Maximal span prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L18-L24

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA
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
open Formalism.ConjugateSelfDual
variable {F : Type*} [Field F] [NumberField F]

theorem ReciprocityTheory.Gal.isMaximal_span_prime (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {(l : ℤ)}).IsMaximal := by sorry
