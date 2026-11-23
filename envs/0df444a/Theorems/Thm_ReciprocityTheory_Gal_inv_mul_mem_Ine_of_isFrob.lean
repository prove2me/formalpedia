-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_inv_mul_mem_Ine_of_isFrob
-- name    : ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:53.946322+00:00
-- url     : https://prove2.me/theorems/01d36f7b-0c19-4f66-93ce-710642344c9b
-- title:
--   Gal: inv mul mem Ine of is Frob
-- statement:
--   The Gal construction uses the inv mul mem Ine of is Frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L239-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L239-L250

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
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
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob {A : ValuationSubring (Ω)} {q : ℕ} {σ τ : G F Ω}
    (hσ : IsFrob A q σ) (hτ : IsFrob A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by sorry
