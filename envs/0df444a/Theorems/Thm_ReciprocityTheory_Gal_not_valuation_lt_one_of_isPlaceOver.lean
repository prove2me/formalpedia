-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_not_valuation_lt_one_of_isPlaceOver
-- name    : ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:58.458017+00:00
-- url     : https://prove2.me/theorems/93c0fb1d-89f4-4f25-a29a-ce1820ad9dfc
-- title:
--   Gal: not valuation lt one of is Place Over
-- statement:
--   The Gal construction uses the not valuation lt one of is Place Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L189-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L189-L197

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

theorem ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver {l : ℕ} {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    (n : ℕ) : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by sorry
