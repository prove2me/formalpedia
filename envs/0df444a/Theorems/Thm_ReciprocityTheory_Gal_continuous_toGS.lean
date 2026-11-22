-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_continuous_toGS
-- name    : ReciprocityTheory.Gal.continuous_toGS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:34.036716+00:00
-- url     : https://prove2.me/theorems/d01bebc6-96d2-492d-a379-fc0e98e97238
-- title:
--   Gal: continuous to GS
-- statement:
--   The Gal construction uses the continuous to GS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L148-L150

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
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable (Ω)

theorem ReciprocityTheory.Gal.continuous_toGS : Continuous (toGS Ω S) := by sorry
