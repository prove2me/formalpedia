-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_one_lt_normV
-- name    : ReciprocityTheory.Gal.one_lt_normV
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:08.830637+00:00
-- url     : https://prove2.me/theorems/0796e762-c0b1-46a6-9f38-a3ca689a835d
-- title:
--   Gal: one lt norm V
-- statement:
--   The Gal construction uses the one lt norm V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalE.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/GlobalE.lean#L85-L96

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalEA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise Polynomial
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp
variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

theorem ReciprocityTheory.Gal.one_lt_normV (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by sorry
