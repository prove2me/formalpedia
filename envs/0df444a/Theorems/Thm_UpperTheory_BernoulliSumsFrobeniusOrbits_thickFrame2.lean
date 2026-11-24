-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_thickFrame2
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:46.338267+00:00
-- url     : https://prove2.me/theorems/67cf62bb-2ab1-4f85-9a66-718ae8daf8cf
-- title:
--   Bernoulli Sums Frobenius Orbits: thick Frame2
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the thick Frame2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean#L29-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean#L29-L198

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_ThickFrame2Large
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2 :
    ∃ CT : ℝ, 0 < CT ∧ ∀ eps Co CL : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (φ : Formalism.HC.Frame) (Lw : ℕ), 2 ≤ Lw →
      (Lw : ℝ) ≤ CL * Real.log x → (φ.o : ℝ) ≤ Co → x ^ hE eps / 2 ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ Co * x ^ hE eps →
      ∃ T2 : Finset ℕ, (∀ s ∈ T2, 4 * Lw * s < φ.n0) ∧ Formalism.FrobeniusOrbits.NoRel T2 Lw ∧
        (φ.n0 : ℝ) * Real.exp (-(CT * Real.sqrt (Real.log (φ.n0 : ℝ) * Real.log Lw))) / Lw ≤ T2.card ∧
        x ^ (-eps) * φ.ord ≤ (T2.card : ℝ) ∧ 4 * Lw * T2.card ≤ φ.n0 := by sorry
