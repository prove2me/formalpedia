-- Prove2me | Theorems.Thm_UpperTheory_Mu_unitary_integral_finite_and_ncard_le
-- name    : UpperTheory.Mu.unitary_integral_finite_and_ncard_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:19.394887+00:00
-- url     : https://prove2.me/theorems/9df09c58-c211-4998-9a41-1b63021c09cd
-- title:
--   Mu: unitary integral finite and ncard le
-- statement:
--   The Mu construction uses the unitary integral finite and ncard le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean#L115-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RootsOfUnity/Monomial.lean#L115-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]

theorem UpperTheory.Mu.unitary_integral_finite_and_ncard_le [StarRing K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ) :
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ Units.torsionOrder K ^ n * n.factorial := by sorry
