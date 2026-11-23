-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_liesOver_span_iff
-- name    : ReciprocityTheory.Gal.liesOver_span_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:47.82411+00:00
-- url     : https://prove2.me/theorems/fc481a4a-0733-4539-b756-a12bf6d21c7c
-- title:
--   Gal: lies Over span iff
-- statement:
--   The Gal construction uses the lies Over span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L26-L40

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

theorem ReciprocityTheory.Gal.liesOver_span_iff (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 F)) [P.IsPrime] :
    P.LiesOver (Ideal.span {(l : ℤ)}) ↔ ((l : ℕ) : 𝓞 F) ∈ P := by sorry
