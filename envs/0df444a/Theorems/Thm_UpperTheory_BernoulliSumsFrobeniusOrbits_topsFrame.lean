-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_topsFrame
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.topsFrame
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:15.021308+00:00
-- url     : https://prove2.me/theorems/60817615-00e0-5b53-bc22-6f5a3888a678
-- title:
--   Bernoulli Sums Frobenius Orbits: tops Frame
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the tops Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/topsFrame.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/topsFrame.lean#L9-L41

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsGroup
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsFrame
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_topsGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsFrame :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ (φ : Formalism.HC.Frame) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ Co * x ^ hE eps → (φ.o : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : φ.A → φ.A → φ.A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → φ.A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset φ.A, dE eps x * φ.ord / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * φ.ord ∧
        φ.Shares TT (x ^ (-1 + eps)) ∧
        ∑ p ∈ PP, ω p * (({t : φ.A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * φ.ord * ∑ p ∈ PP, ω p := by sorry
