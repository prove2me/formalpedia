-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_continuous_locHom
-- name    : ReciprocityTheory.Gal.continuous_locHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:59.395807+00:00
-- url     : https://prove2.me/theorems/5d8cc47b-a21b-4b45-9411-a265badb0669
-- title:
--   Gal: continuous loc Hom
-- statement:
--   The Gal construction uses the continuous loc Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L155-L156

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

theorem ReciprocityTheory.Gal.continuous_locHom (A : ValuationSubring (Ω)) :
    Continuous (locHom S A) := by sorry
