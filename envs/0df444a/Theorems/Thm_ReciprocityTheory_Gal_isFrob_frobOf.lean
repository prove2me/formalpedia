-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_isFrob_frobOf
-- name    : ReciprocityTheory.Gal.isFrob_frobOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:36:29.47323+00:00
-- url     : https://prove2.me/theorems/689ed647-337a-4a68-94d9-e13d9d54c03a
-- title:
--   Gal: is Frob frob Of
-- statement:
--   The Gal construction uses the is Frob frob Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L350-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L350-L351

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
variable (Ω)

theorem ReciprocityTheory.Gal.isFrob_frobOf [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) :
    IsFrob (placeOf Ω v) (normV v) (frobOf Ω v) := by sorry
