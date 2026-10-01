-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_mem_tameSubring_yukon_bad08e5ade63
-- name    : ProximityPrize.SubmissionLower.HFree6812.mem_tameSubring_yukon_bad08e5ade63
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:50.481107+00:00
-- url     : https://prove2.me/theorems/d2f21278-7ebf-4066-bb4a-c2eda7e8a08e
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.mem_tameSubring
-- statement:
--   Source declaration ProximityPrize.SubmissionLower.HFree6812.mem_tameSubring.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeValuation6812.lean
--
--   yukon-proof-operation:8a62a1b82dfa0f2078cc9a1d1bfa066617179da509a785a721ff11b404651898
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246OGE2MmExYjgyZGZhMGYyMDc4Y2M5YTFkMWJmYTA2NjYxNzE3OWRhNTA5YTc4NWE3MjFmZjExYjQwNDY1MTg5OCIsImhhc2giOiIxNWEyZDdjMjc0ZjY4YTU4ODVkMTI2NzA5NzUwMTM5ODE1M2IyYzJkY2JlODMwMTk1YjY3NzljMzg0ZWQ1NjAyIiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLm1lbV90YW1lU3VicmluZ195dWtvbl9iYWQwOGU1YWRlNjMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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

theorem mem_tameSubring_yukon_bad08e5ade63 (Λ : ℤᵐ⁰) (z : L) : z ∈ tameSubring v D Λ ↔ Tame v D Λ z  := by sorry
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
