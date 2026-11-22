-- Prove2me | Theorems.Thm_ReciprocityTheory_Gal_cycZ_toZModPow_eq
-- name    : ReciprocityTheory.Gal.cycZ_toZModPow_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:28:27.681035+00:00
-- url     : https://prove2.me/theorems/52434d3f-b02f-4c2b-a744-0b3447e5bc87
-- title:
--   Gal: cyc Z to ZMod Pow eq
-- statement:
--   The Gal construction uses the cyc Z to ZMod Pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L199-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GaloisValuations/Global.lean#L199-L229

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

theorem ReciprocityTheory.Gal.cycZ_toZModPow_eq [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} {q : ℕ}
    (hσ : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) (n : ℕ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow n (q : ℤ_[l]) := by sorry
