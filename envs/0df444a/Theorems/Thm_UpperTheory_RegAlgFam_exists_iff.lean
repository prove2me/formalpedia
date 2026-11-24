-- Prove2me | Theorems.Thm_UpperTheory_RegAlgFam_exists_iff
-- name    : UpperTheory.RegAlgFam.exists_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:00:08.293552+00:00
-- url     : https://prove2.me/theorems/15409f76-ae08-4324-a5d4-56b9c29a21ea
-- title:
--   Reg Alg Fam: exists iff
-- statement:
--   The Reg Alg Fam construction uses the exists iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/RegAlgFam.lean#L17-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/RegAlgFam.lean#L17-L69

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_RegAlgFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open UpperTheory UpperTheory.RegAlgFam

theorem UpperTheory.RegAlgFam.exists_iff {F : Type*} [Field F] [IsTotallyComplex F] {n : ℕ} (μ : (F →+* ℂ) → Multiset ℂ)
    (hc : ∀ τ, (μ τ).card = n) :
    (∃ t : Reformulated.AlgebraicInfinityType.InfinityType F n, t.IsRegularAlgebraic ∧ ∀ τ, t.exponents τ = μ τ) ↔
      ∀ τ, (μ τ).Nodup ∧ ∀ z ∈ μ τ, ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by sorry
