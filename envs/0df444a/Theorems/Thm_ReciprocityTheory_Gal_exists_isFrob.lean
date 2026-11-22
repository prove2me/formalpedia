-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_exists_isFrob
-- name    : ReciprocityTheory.Gal.exists_isFrob
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:41.121804+00:00
-- url     : https://prove2.me/theorems/3e508f6b-3a74-4bbb-be47-de9038663908
-- title:
--   Gal: exists is Frob
-- statement:
--   The Gal construction uses the exists is Frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L345-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L345-L347

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

theorem ReciprocityTheory.Gal.exists_isFrob [IsAlgClosure F Ω] {A : ValuationSubring (Ω)} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : ∃ σ : G F Ω, IsFrob A (normV v) σ := by sorry
