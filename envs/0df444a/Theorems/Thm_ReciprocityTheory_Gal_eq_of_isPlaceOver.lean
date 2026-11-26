-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_eq_of_isPlaceOver
-- name    : ReciprocityTheory.Gal.eq_of_isPlaceOver
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:44.064696+00:00
-- url     : https://prove2.me/theorems/1d7259a8-8f15-41de-bace-d7f9b0f1cb0f
-- title:
--   Gal: eq of is Place Over
-- statement:
--   The Gal construction uses the eq of is Place Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L231-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L231-L237

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

theorem ReciprocityTheory.Gal.eq_of_isPlaceOver {A : ValuationSubring (Ω)} {v v' : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : v = v' := by sorry
