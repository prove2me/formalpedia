-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_cycZ_of_isFrob
-- name    : ReciprocityTheory.Gal.cycZ_of_isFrob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:27.921032+00:00
-- url     : https://prove2.me/theorems/fde84223-0dce-4bb7-97e5-22233eef6c71
-- title:
--   Gal: cyc Z of is Frob
-- statement:
--   The Gal construction uses the cyc Z of is Frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L364-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L364-L368

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

theorem ReciprocityTheory.Gal.cycZ_of_isFrob [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : IsFrob A (normV v) σ) : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV v : ℤ_[l]) := by sorry
