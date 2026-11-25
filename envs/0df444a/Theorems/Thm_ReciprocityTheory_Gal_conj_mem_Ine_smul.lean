-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_conj_mem_Ine_smul
-- name    : ReciprocityTheory.Gal.conj_mem_Ine_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:14.740482+00:00
-- url     : https://prove2.me/theorems/46e3f345-d915-5b2f-b481-165dcb99e5fa
-- title:
--   Gal: conj mem Ine smul
-- statement:
--   The Gal construction uses the conj mem Ine smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L104-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/ArithOfA.lean#L104-L121

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
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem ReciprocityTheory.Gal.conj_mem_Ine_smul {A : ValuationSubring Ω} {γ σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) :
    γ * σ * γ⁻¹ ∈ Ine (F := F) (γ • A) := by sorry
