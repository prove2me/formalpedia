-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_derivation_order_of_basis_yukon_abb914525d86
-- name    : ProximityPrize.SubmissionLower.HFree6812.derivation_order_of_basis_yukon_abb914525d86
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:27.168975+00:00
-- url     : https://prove2.me/theorems/23750111-e40f-47c4-a8ea-2a2e3143a172
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.derivation_order_of_basis
-- statement:
--   (i) in the form of the task statement: `t i ∈ O_v` with `pole (D (t i)) ≤ s`, the
--   residue field separable over `K(t̄)`, crude continuity, `s ≤ θ` and `1 - ord (Dπ) ≤ θ`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeValuation6812.lean
--
--   yukon-proof-operation:cad1e80c62776147152cd0e56c6242519e6c97c48d0d7f8897690b548d43e2a7
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Y2FkMWU4MGM2Mjc3NjE0NzE1MmNkMGU1NmM2MjQyNTE5ZTZjOTdjNDhkMGQ3Zjg4OTc2OTBiNTQ4ZDQzZTJhNyIsImhhc2giOiJiNmRhOWE0MGZlMmQ2ZTVlOWQyMGU2NzVhNDNkMjI0NDg1YzM3N2QyNmY0ZGRjY2Y1MDg3N2FhZDQ5N2Q3MWVjIiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLmRlcml2YXRpb25fb3JkZXJfb2ZfYmFzaXNfeXVrb25fYWJiOTE0NTI1ZDg2IiwiZW52aXJvbm1lbnQiOnsibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQiLCJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEifSwidGFnIjoiYmV0dGVyLWNvZGVzIn0]

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
section Bridges
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)

/-- (i) in the form of the task statement: `t i ∈ O_v` with `pole (D (t i)) ≤ s`, the
residue field separable over `K(t̄)`, crude continuity, `s ≤ θ` and `1 - ord (Dπ) ≤ θ`. -/
theorem derivation_order_of_basis_yukon_abb914525d86 [v.IsTrivialOn K] {ι : Type*} (t : ι → L)
    (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s) (hsθ : s ≤ θ)
    (hπθ : v (D π) ≤ exp (θ - 1)) (ht : ∀ i, v (t i) ≤ 1) (hDt : ∀ i, v (D (t i)) ≤ exp s)
    (C : ℤ) (hcont : CrudeBound v D C)
    [Algebra.IsSeparable (Subfield.closure (residue v '' (Set.range (algebraMap K L) ∪
      Set.range t))) (IsLocalRing.ResidueField v.valuationSubring)] (f : L) :
    v (D f) ≤ exp θ * v f  := by sorry
end Bridges
end HFree6812
end SubmissionLower
end ProximityPrize
