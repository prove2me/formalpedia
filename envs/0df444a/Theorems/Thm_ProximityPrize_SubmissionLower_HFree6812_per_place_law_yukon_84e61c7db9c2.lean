-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_per_place_law_yukon_84e61c7db9c2
-- name    : ProximityPrize.SubmissionLower.HFree6812.per_place_law_yukon_84e61c7db9c2
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:59.340996+00:00
-- url     : https://prove2.me/theorems/2db30b79-4a02-41df-96d2-8da1ecb43e0d
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.per_place_law
-- statement:
--   The per-place law: with `θ ≤ T + n₁` (`multiplicity_theorem`), the dichotomy, `θ ≥ 2`,
--   `0 ≤ T` and `T ≤ ord H` (affine places: `T = pole (G/H) ≤ ord H`), `3 θ ≤ 4 T + 2 ord H`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeLocal6812.lean
--
--   yukon-proof-operation:f99f209a7883182a618a21314e0d20963ebf9cd0612d5aa4359a5740f3ed9087
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Zjk5ZjIwOWE3ODgzMTgyYTYxOGEyMTMxNGUwZDIwOTYzZWJmOWNkMDYxMmQ1YWE0MzU5YTU3NDBmM2VkOTA4NyIsImhhc2giOiIyMzQzMjM5YzlkYjhiZGVjYjkzZTVhN2JiMGY2NjA2Zjc4YmYzYTU1NzEzZDkxM2Y1NWI5MWQ4YTAwNzMxOTY3Iiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLnBlcl9wbGFjZV9sYXdfeXVrb25fODRlNjFjN2RiOWMyIiwiZW52aXJvbm1lbnQiOnsibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQiLCJ0b29sY2hhaW4iOiJsZWFucHJvdmVyL2xlYW40OnY0LjMzLjEifSwidGFnIjoiYmV0dGVyLWNvZGVzIn0]

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

/-- The per-place law: with `θ ≤ T + n₁` (`multiplicity_theorem`), the dichotomy, `θ ≥ 2`,
`0 ≤ T` and `T ≤ ord H` (affine places: `T = pole (G/H) ≤ ord H`), `3 θ ≤ 4 T + 2 ord H`. -/
theorem per_place_law_yukon_84e61c7db9c2 (θ T h : ℤ) (n₁ : ℕ) (hθ : θ ≤ T + n₁)
    (hd : n₁ ≤ 1 ∨ 3 * (n₁ : ℤ) ≤ 2 * h) (h2θ : 2 ≤ θ) (hT : 0 ≤ T) (hTh : T ≤ h) :
    3 * θ ≤ 4 * T + 2 * h  := by sorry
end HFree6812
end SubmissionLower
end ProximityPrize
