-- Prove2me | Theorems.Thm_UpperTheory_T3_typePrimesN
-- name    : UpperTheory.T3.typePrimesN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:44.415676+00:00
-- url     : https://prove2.me/theorems/2d290c6a-d41f-485d-af33-20c51839d3fd
-- title:
--   T3: type Primes N
-- statement:
--   The T3 construction uses the type Primes N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/typePrimesN.lean#L78-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ShortNorms/typePrimesN.lean#L78-L129

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_normPrimesN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_typePrimesN
import Theorems.Thm_UpperTheory_T3_normPrimesN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Mem.An
open UpperTheory UpperTheory.T3

theorem UpperTheory.T3.typePrimesN :
    ShortNorm → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d k r : ℕ, ModAt x eps N d → 1 ≤ k → 1 ≤ r → (r : ℝ) ≤ x ^ (5 : ℝ) →
      ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((k : ℝ) * Real.exp (x ^ eps)) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((k : ℝ) * Real.exp (x ^ eps)) ^ 8 ∧
        NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB r (g 0)) (Formalism.CyclotomicNorms.BB r (g 1)) := by sorry
