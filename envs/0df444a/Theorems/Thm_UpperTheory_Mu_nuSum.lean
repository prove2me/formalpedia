-- Prove2me | Theorems.Thm_UpperTheory_Mu_nuSum
-- name    : UpperTheory.Mu.nuSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:51.008941+00:00
-- url     : https://prove2.me/theorems/ea0ade3d-59a9-54f5-aa54-faef792f7056
-- title:
--   Mu: nu Sum
-- statement:
--   The Mu construction uses the nu Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/SumFactorizationMulLogLe.lean#L31-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/SumFactorizationMulLogLe.lean#L31-L59

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuSumApprox
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuLe
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_NuQDUnit
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_SumFactorizationMulLogLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HC KStar.Tree

theorem UpperTheory.Mu.nuSum :
    ∀ (φ : Frame) (H : HostRaw φ) (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (n : ℕ), Odd n → ¬ (H.q - 1) / 2 ∣ n → ¬ (H.d - 1) / 2 ∣ n → ∀ ν : ℕ → ℕ, (∀ (l : ℕ) [Fact l.Prime], ν l = nuOf l (cyc l H.E Ω) n) → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (ν l : ℝ) * Real.log l ≤ Real.log H.QS + Real.log n := by sorry
