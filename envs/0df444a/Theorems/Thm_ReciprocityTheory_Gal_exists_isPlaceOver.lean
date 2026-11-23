-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_exists_isPlaceOver
-- name    : ReciprocityTheory.Gal.exists_isPlaceOver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:31.149167+00:00
-- url     : https://prove2.me/theorems/a317bd0f-6651-4462-ada3-5ebd71fbb791
-- title:
--   Gal: exists is Place Over
-- statement:
--   The Gal construction uses the exists is Place Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L265-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L265-L335

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

theorem ReciprocityTheory.Gal.exists_isPlaceOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ A : ValuationSubring (Ω), IsPlaceOver A v := by sorry
