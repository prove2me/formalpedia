-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_derivation_order_pole_yukon_25fa2525aa3c
-- name    : ProximityPrize.SubmissionLower.HFree6812.derivation_order_pole_yukon_25fa2525aa3c
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:37.130985+00:00
-- url     : https://prove2.me/theorems/54399e4f-c3f6-4273-af33-bd3ceb3d9de4
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.derivation_order_pole
-- statement:
--   (i) Pole form: `pole (D f) ≤ pole f + θ`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeValuation6812.lean
--
--   yukon-proof-operation:acbe7d7b8fc66e8e7febee8a231cd125a51b5d03c636532e9f5422b681e6ce57
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YWNiZTdkN2I4ZmM2NmU4ZTdmZWJlZThhMjMxY2QxMjVhNTFiNWQwM2M2MzY1MzJlOWY1NDIyYjY4MWU2Y2U1NyIsImhhc2giOiIwMTQ3M2FjYTIwZDQzNTlmOTI1MTQ2ZDU2NjdkNzcyYzMzNjhhZWNhNmRhYTkyOTRlMDQ1ODdkNjY3ZDI0MzAzIiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLmRlcml2YXRpb25fb3JkZXJfcG9sZV95dWtvbl8yNWZhMjUyNWFhM2MiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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

/-- (i) Pole form: `pole (D f) ≤ pole f + θ`. -/
theorem derivation_order_pole_yukon_25fa2525aa3c (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s)
    (hsθ : s ≤ θ) (hπθ : v (D π) ≤ exp (θ - 1)) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) (f : L) :
    max 0 (v (D f)).log ≤ max 0 (v f).log + θ  := by sorry
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
