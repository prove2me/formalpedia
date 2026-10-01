-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_sum_charge_le_yukon_936c0fd0929f
-- name    : ProximityPrize.SubmissionLower.HFree6812.sum_charge_le_yukon_936c0fd0929f
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:56:02.794108+00:00
-- url     : https://prove2.me/theorems/bbd28f1e-06e9-4ae8-ad9b-86d47e49e2a5
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.sum_charge_le
-- statement:
--   Summation over the places of a slice component: a charge `c` that satisfies the
--   per-place law at contributing places and vanishes elsewhere obeys
--   `3 Σ c ≤ 4 Σ T + 2 Σ h`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeLocal6812.lean
--
--   yukon-proof-operation:fcc6fb071e2e70e555a47d4a8d59bad68d4210df70126e7257536fc06d3c9a31
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZmNjNmZiMDcxZTJlNzBlNTU1YTQ3ZDRhOGQ1OWJhZDY4ZDQyMTBkZjcwMTI2ZTcyNTc1MzZmYzA2ZDNjOWEzMSIsImhhc2giOiJhOGJkMDFjMTg1NjhiMTJlYjlmMmIwNzE2OGY0NWY5OGQ5N2NjZjY0ZDBmYTQ0YTg0ZDU4OTU4YTc4MTE4MzM0Iiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLnN1bV9jaGFyZ2VfbGVfeXVrb25fOTM2YzBmZDA5MjlmIiwiZW52aXJvbm1lbnQiOnsibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQiLCJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEifSwidGFnIjoiYmV0dGVyLWNvZGVzIn0]

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

/-- Summation over the places of a slice component: a charge `c` that satisfies the
per-place law at contributing places and vanishes elsewhere obeys
`3 Σ c ≤ 4 Σ T + 2 Σ h`. -/
theorem sum_charge_le_yukon_936c0fd0929f {ι : Type*} (W : Finset ι) (c T h : ι → ℤ)
    (hT : ∀ i ∈ W, 0 ≤ T i) (hh : ∀ i ∈ W, 0 ≤ h i)
    (hc : ∀ i ∈ W, c i = 0 ∨ 3 * c i ≤ 4 * T i + 2 * h i) :
    3 * ∑ i ∈ W, c i ≤ 4 * ∑ i ∈ W, T i + 2 * ∑ i ∈ W, h i  := by sorry
end HFree6812
end SubmissionLower
end ProximityPrize
