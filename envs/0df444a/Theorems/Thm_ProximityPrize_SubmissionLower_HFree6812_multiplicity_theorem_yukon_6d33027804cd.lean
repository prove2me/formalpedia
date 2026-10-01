-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_multiplicity_theorem_yukon_6d33027804cd
-- name    : ProximityPrize.SubmissionLower.HFree6812.multiplicity_theorem_yukon_6d33027804cd
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T18:05:50.347965+00:00
-- url     : https://prove2.me/theorems/e1176594-5d54-4c7b-864a-45015eb88b2d
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.multiplicity_theorem
-- statement:
--   (ii) The local multiplicity theorem: if `R ⊆ O_v`, `D R ⊆ R + R σ` with
--   `pole σ ≤ T`, `s ≤ T`, and some `f ∈ R` has `ord f = n₁` with `n₁` a unit in `K`, then
--   `θ := T + n₁` satisfies the derivation-order lemma.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeValuation6812.lean
--
--   yukon-proof-operation:38bca5216e78e405323300233196442289f07e80fb31680ce2207bc2c939b167
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MzhiY2E1MjE2ZTc4ZTQwNTMyMzMwMDIzMzE5NjQ0MjI4OWYwN2U4MGZiMzE2ODBjZTIyMDdiYzJjOTM5YjE2NyIsImhhc2giOiJlNzBlOTgzNTllY2FmZDIwZjUwZTliY2U1MjA2Y2JjZTJjMWY0MTFhYWE4MjIyM2FhYTIzNTRiMDY3Y2I3YzI3Iiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLm11bHRpcGxpY2l0eV90aGVvcmVtX3l1a29uXzZkMzMwMjc4MDRjZCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable


import Init
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1
set_option backward.isDefEq.respectTransparency.types false
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial
section Core
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)

/-- (ii) The local multiplicity theorem: if `R ⊆ O_v`, `D R ⊆ R + R σ` with
`pole σ ≤ T`, `s ≤ T`, and some `f ∈ R` has `ord f = n₁` with `n₁` a unit in `K`, then
`θ := T + n₁` satisfies the derivation-order lemma. -/
theorem multiplicity_theorem_yukon_6d33027804cd [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s : ℤ)
    (hs : 0 ≤ s) (C : ℤ) (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s))
    (R : Subring L) (hR : ∀ r ∈ R, v r ≤ 1) (σ : L) (T : ℤ) (hT : 0 ≤ T)
    (hσ : v σ ≤ exp T) (hDR : ∀ r ∈ R, ∃ a ∈ R, ∃ b ∈ R, D r = a + b * σ) (hsT : s ≤ T)
    (f : L) (hfR : f ∈ R) (n : ℕ) (hn : (n : K) ≠ 0) (hf : v f = exp (-(n : ℤ))) :
    v (D π) ≤ exp (T + n - 1) ∧ ∀ g : L, v (D g) ≤ exp (T + n) * v g  := by sorry
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
