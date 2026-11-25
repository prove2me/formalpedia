-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_orbit_terms
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:21.848921+00:00
-- url     : https://prove2.me/theorems/475daff9-c6f3-53a9-b896-64ad792263ba
-- title:
--   Bernoulli Sums Frobenius Orbits: orbit terms
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the orbit terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/orbitTerms.lean#L97-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/orbitTerms.lean#L97-L261

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLowBounds
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
set_option maxHeartbeats 400000

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_terms :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ n L₂ : ℕ, x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ Co * x ^ hE eps →
      (L₂ : ℝ) ≤ Lb →
      (Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x + 1) * ((6 * rE eps + 1) * Formalism.MainNotions.G.goodU (dE eps x)) ≤ n ∧
      (n : ℝ) * (L₂.choose (KE eps) : ℝ) * dE eps x ^ KE eps +
        n * (1 - markedLow (dE eps x) (rE eps) (Formalism.MainNotions.G.goodU (dE eps x))) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (rE eps) (hE eps) x +
        n * binUpper (Formalism.MainNotions.G.goodG' (rE eps) (dE eps x) (hE eps) x) (dE eps x)
          (Formalism.MainNotions.G.orbitWindowCount (rE eps) (dE eps x) (hE eps) x - 1) ≤ Cb * x ^ (-2 : ℝ) := by sorry
