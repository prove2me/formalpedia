-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_topsGroup
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.topsGroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:00.349314+00:00
-- url     : https://prove2.me/theorems/9771c620-a7f6-4feb-b1c3-e521bc8d4e94
-- title:
--   Bernoulli Sums Frobenius Orbits: tops Group
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the tops Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean#L64-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/topsGroup.lean#L64-L143

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_select
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitSum
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_SharesOfCounts
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitTerms
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_NotGoodLe
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_topsGroup
import Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_select

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Classical

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsGroup :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀,
      ∀ (A : Type) [Fintype A] [DecidableEq A] [AddCommGroup A] (A0 : AddSubgroup A) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (Fintype.card A : ℝ) → (Fintype.card A : ℝ) ≤ Co * x ^ hE eps → (A0.index : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : A → A → A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset A, dE eps x * Fintype.card A / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * Fintype.card A ∧
        (∀ γ : A, |((TT.filter fun t => t - γ ∈ A0).card : ℝ) -
          (if γ ∈ A0 then 4 else 3) / (3 * (A0.index : ℝ) + 1) * (TT.card : ℝ)| ≤ x ^ (-1 + eps) * (TT.card : ℝ)) ∧
        ∑ p ∈ PP, ω p * (({t : A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * Fintype.card A * ∑ p ∈ PP, ω p := by sorry
