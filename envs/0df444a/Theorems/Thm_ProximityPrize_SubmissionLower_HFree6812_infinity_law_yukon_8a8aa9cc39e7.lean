-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_infinity_law_yukon_8a8aa9cc39e7
-- name    : ProximityPrize.SubmissionLower.HFree6812.infinity_law_yukon_8a8aa9cc39e7
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:49.266227+00:00
-- url     : https://prove2.me/theorems/74cd79ee-be45-4e95-a4d4-9b650893a7b4
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.infinity_law
-- statement:
--   The law at a place at infinity (`θ ≤ T`, `h ≥ 0`).
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeLocal6812.lean
--
--   yukon-proof-operation:507060896ec70942540babb52eb8a1e043c2c0117930a5a78ff77502ddfe77c5
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NTA3MDYwODk2ZWM3MDk0MjU0MGJhYmI1MmViOGExZTA0M2MyYzAxMTc5MzBhNWE3OGZmNzc1MDJkZGZlNzdjNSIsImhhc2giOiI5MjNjNmVmYzJiM2Y4N2FkZGJhNDQzOGU0NjQ1ODhmMjgyYzUyZGFiMWIwOTQyMTcwZTk2MmM2YWE3Mzk1NmRlIiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLmluZmluaXR5X2xhd195dWtvbl84YThhYTljYzM5ZTciLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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

/-- The law at a place at infinity (`θ ≤ T`, `h ≥ 0`). -/
theorem infinity_law_yukon_8a8aa9cc39e7 (θ T h : ℤ) (hθ : θ ≤ T) (hT : 0 ≤ T) (hh : 0 ≤ h) :
    3 * θ ≤ 4 * T + 2 * h  := by sorry
end HFree6812
end SubmissionLower
end ProximityPrize
