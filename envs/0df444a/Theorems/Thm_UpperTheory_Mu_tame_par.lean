-- Prove2me | Theorems.Thm_UpperTheory_Mu_tame_par
-- name    : UpperTheory.Mu.tame_par
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:03.973918+00:00
-- url     : https://prove2.me/theorems/f8fceaed-9f2b-50db-91f5-adc7d7ef22da
-- title:
--   Mu: tame par
-- statement:
--   The Mu construction uses the tame par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/ResidueEisenstein.lean#L52-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/ResidueEisenstein.lean#L52-L66

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_ResidueEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Mu
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem UpperTheory.Mu.tame_par {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    {I : Type} [Fintype I] (φ : I → L →+* ℂ) (e : I → ℤ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      (∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i) * ((θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by sorry
