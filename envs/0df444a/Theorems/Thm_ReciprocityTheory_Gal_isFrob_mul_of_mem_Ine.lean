-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isFrob_mul_of_mem_Ine
-- name    : ReciprocityTheory.Gal.isFrob_mul_of_mem_Ine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:08.04163+00:00
-- url     : https://prove2.me/theorems/c4a4a43b-3169-4d3a-b507-35eac50f4a21
-- title:
--   Gal: is Frob mul of mem Ine
-- statement:
--   The Gal construction uses the is Frob mul of mem Ine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L252-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L252-L261

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

theorem ReciprocityTheory.Gal.isFrob_mul_of_mem_Ine {A : ValuationSubring (Ω)} {q : ℕ} {σ ι : G F Ω}
    (hσ : IsFrob A q σ) (hι : ι ∈ Ine (F := F) A) : IsFrob A q (σ * ι) := by sorry
