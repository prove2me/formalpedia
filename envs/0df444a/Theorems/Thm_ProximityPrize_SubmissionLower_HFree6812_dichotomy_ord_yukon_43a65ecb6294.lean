-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_dichotomy_ord_yukon_43a65ecb6294
-- name    : ProximityPrize.SubmissionLower.HFree6812.dichotomy_ord_yukon_43a65ecb6294
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:46.760338+00:00
-- url     : https://prove2.me/theorems/8602dcb3-57ba-4455-bd8a-343b02194b42
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.dichotomy_ord
-- statement:
--   Additive form of the dichotomy when `ord (D₀ F) = h`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeLocal6812.lean
--
--   yukon-proof-operation:35d69dbfcb2a327a757779427cfd05d50862b9253ad49cf9163203bc9285b137
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MzVkNjlkYmZjYjJhMzI3YTc1Nzc3OTQyN2NmZDA1ZDUwODYyYjkyNTNhZDQ5Y2Y5MTYzMjAzYmM5Mjg1YjEzNyIsImhhc2giOiI0M2M1Njc5Njc1ZWJmY2U5N2Q5MWI3NWU1NGVhMzNjMzk1MTM2YTg1NWVjNWIwMTBlM2YyYzhhYzQxZGYzMTQ2Iiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLmRpY2hvdG9teV9vcmRfeXVrb25fNDNhNjVlY2I2Mjk0IiwiZW52aXJvbm1lbnQiOnsibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQiLCJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEifSwidGFnIjoiYmV0dGVyLWNvZGVzIn0]

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


import Init
import Definitions.Def_Yukon_590a300e51c847902c7c8694
set_option backward.isDefEq.respectTransparency.types false
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial

/-- Additive form of the dichotomy when `ord (D₀ F) = h`. -/
theorem dichotomy_ord_yukon_43a65ecb6294 (n₁ : ℕ) (h : ℤ) (x : ℤᵐ⁰) (hx : x = exp (-h))
    (hd : n₁ ≤ 1 ∨ x ^ 2 ≤ exp (-(3 * n₁ : ℤ))) : n₁ ≤ 1 ∨ 3 * (n₁ : ℤ) ≤ 2 * h  := by sorry
end HFree6812
end SubmissionLower
end ProximityPrize
