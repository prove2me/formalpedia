-- Prove2me | Theorems.Thm_UpperTheory_Mu_tame_ext
-- name    : UpperTheory.Mu.tame_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:20.681162+00:00
-- url     : https://prove2.me/theorems/982c7a94-5854-4fd7-8c1c-027ef434a8fc
-- title:
--   Mu: tame ext
-- statement:
--   The Mu construction uses the tame ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/TorsionReduceInjective.lean#L42-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/TorsionReduceInjective.lean#L42-L91

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Classical
noncomputable section
open UpperTheory UpperTheory.Mu

theorem UpperTheory.Mu.tame_ext : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)), ((NumberField.Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal → NumberField.Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal → ∀ ε : NumberField.Units.torsion L →* ℂˣ, ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : NumberField.Units.torsion L, θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom (ζ : (𝓞 L)ˣ)) = ε ζ := by sorry
