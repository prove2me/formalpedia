-- Prove2me | Theorems.Thm_UpperTheory_prod_residue_char_norm_one_unit_eq_one
-- name    : UpperTheory.prod_residue_char_norm_one_unit_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:35.762024+00:00
-- url     : https://prove2.me/theorems/b6e5145a-c95f-4e30-93e9-640ad4525345
-- title:
--   Upper Theory: prod residue char norm one unit eq one
-- statement:
--   The Upper Theory construction uses the prod residue char norm one unit eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdResidueCharNormOneUnitEqOne.lean#L66-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/ProdResidueCharNormOneUnitEqOne.lean#L66-L182

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdResidueCharNormOneUnitEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Pointwise

theorem UpperTheory.prod_residue_char_norm_one_unit_eq_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (p : ℕ), p.Prime →
      ∀ (Q : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ w, w ∈ S ↔ w.under (𝓞 K) = Q) →
      (∀ w ∈ S, Ideal.absNorm w.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ w.asIdeal ^ 2) →
      ∀ (ω : (ZMod p)ˣ →* ℂˣ) (θ : ∀ w : HeightOneSpectrum (𝓞 L), (𝓞 L ⧸ w.asIdeal)ˣ →* ℂˣ),
      (∀ w ∈ S, ∀ (a : ℕ) (ha : a.Coprime p), ∃ b : (𝓞 L ⧸ w.asIdeal)ˣ,
        (b : 𝓞 L ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 L) ∧ θ w b = ω (ZMod.unitOfCoprime a ha)) →
      ∀ u : (𝓞 L)ˣ, Algebra.norm K ((u : 𝓞 L) : L) = 1 →
        ∏ w ∈ S, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom u) = 1 := by sorry
