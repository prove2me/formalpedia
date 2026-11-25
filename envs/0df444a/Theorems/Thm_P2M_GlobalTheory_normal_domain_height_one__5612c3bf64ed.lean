-- Prove2me | Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
-- name    : P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:04.131829+00:00
-- url     : https://prove2.me/theorems/e4fe7e33-94b9-4104-bc8f-56dc17a665a4
-- title:
--   P2 M Global Theory normal domain height one  5612c3bf64ed: P2 M Global Theory normal domain height one  5612c3bf64ed
-- statement:
--   The P2 M Global Theory normal domain height one  5612c3bf64ed construction uses the P2 M Global Theory normal domain height one  5612c3bf64ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L616-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean#L616-L647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory

theorem P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed.{u, v, w} (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (K : Type v) [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      IsDiscreteValuationRing (Localization.AtPrime p) ∧
      ∃ _ : IsDiscreteValuationRing (primeLocalSubalgebra K p),
        ∀ x : K, x ≠ 0 → WithZero.exp (-heightOneOrd_vw p hp x) =
          (IsDiscreteValuationRing.maximalIdeal (primeLocalSubalgebra K p)).valuation K x) ∧
    (∀ x : K, x ∈ (algebraMap A K).range ↔
      ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → x ∈ primeLocalSubalgebra K p) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module A M] [Module.Projective A M],
      Function.Injective (TensorProduct.mk A K M 1) ∧
      ∀ v : K ⊗[A] M, v ∈ LinearMap.range (TensorProduct.mk A K M 1) ↔
        ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
          v ∈ LinearMap.range ((primeLocalSubalgebra K p).val.toLinearMap.rTensor M)) ∧
    (∀ x : K, x ≠ 0 → {p : PrimeSpectrum A |
      ∃ hp : p.asIdeal.height = 1, heightOneOrd_vw p.asIdeal hp x ≠ 0}.Finite) ∧
    (∀ x y : K, x ≠ 0 → y ≠ 0 →
      (∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
        heightOneOrd_vw p hp x = heightOneOrd_vw p hp y) → ∃ u : Aˣ, u • y = x) ∧
    (∀ a : A, a ≠ 0 → ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {a}), p.height = 1) := by sorry

alias «GlobalTheory».«normal_domain_height_one».«» := P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
