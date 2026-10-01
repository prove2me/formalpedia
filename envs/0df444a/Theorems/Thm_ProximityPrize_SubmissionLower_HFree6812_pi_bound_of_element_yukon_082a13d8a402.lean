-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_pi_bound_of_element_yukon_082a13d8a402
-- name    : ProximityPrize.SubmissionLower.HFree6812.pi_bound_of_element_yukon_082a13d8a402
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:57.100349+00:00
-- url     : https://prove2.me/theorems/636c077f-9bdc-4fd1-8176-021c02e176f0
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.pi_bound_of_element
-- statement:
--   (ii) One element `f` with `ord f = n`, `pole (D f) ≤ T`, `n` a unit in `K`, and
--   `s ≤ T` force `1 - ord (Dπ) ≤ T + n`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeValuation6812.lean
--
--   yukon-proof-operation:5899cd743ca98ebb6775f39c4c6d0c998877af37701fd05a7dc68c0c551927d8
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NTg5OWNkNzQzY2E5OGViYjY3NzVmMzljNGM2ZDBjOTk4ODc3YWYzNzcwMWZkMDVhN2RjNjhjMGM1NTE5MjdkOCIsImhhc2giOiI3ZWE5YjIyYmMxZWE3YTAzMmYwMDBjMzA2MjEyYzM5OTIwZGYxMzU5YmVhMWQ5OWY2NDM3YzA1YjJlMzVjZTcxIiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLnBpX2JvdW5kX29mX2VsZW1lbnRfeXVrb25fMDgyYTEzZDhhNDAyIiwiZW52aXJvbm1lbnQiOnsibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQiLCJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEifSwidGFnIjoiYmV0dGVyLWNvZGVzIn0]

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

/-- (ii) One element `f` with `ord f = n`, `pole (D f) ≤ T`, `n` a unit in `K`, and
`s ≤ T` force `1 - ord (Dπ) ≤ T + n`. -/
theorem pi_bound_of_element_yukon_082a13d8a402 [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s T : ℤ)
    (hsT : s ≤ T) (hint : ∀ u : L, v u ≤ 1 → v (D u) ≤ max (exp s) (v (D π)))
    (f : L) (n : ℕ) (hn : (n : K) ≠ 0) (hf : v f = exp (-(n : ℤ)))
    (hDf : v (D f) ≤ exp T) :
    v (D π) ≤ exp (T + n - 1)  := by sorry
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
