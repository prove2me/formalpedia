-- Prove2me | Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_derivation_order_iterate_yukon_37deb23af724
-- name    : ProximityPrize.SubmissionLower.HFree6812.derivation_order_iterate_yukon_37deb23af724
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-30T17:55:23.350984+00:00
-- url     : https://prove2.me/theorems/01d19874-b994-42db-a5f0-fc1953ebb2cb
-- title:
--   ProximityPrize.SubmissionLower.HFree6812.derivation_order_iterate
-- statement:
--   (i) Iterated: `ord (Dᵏ f) ≥ ord f - k θ`.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeValuation6812.lean
--
--   yukon-proof-operation:274dfb1783eec354e64e81799feb34b413f3e3fff3b35443b86871da5b4700d3
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246Mjc0ZGZiMTc4M2VlYzM1NGU2NGU4MTc5OWZlYjM0YjQxM2YzZTNmZmYzYjM1NDQzYjg2ODcxZGE1YjQ3MDBkMyIsImhhc2giOiJkNDU2YmMyNzFhYTdkMDFiYzNhM2YyMTBkNDNlNzU1NTRhMzkwZDhhYWJjNzIzOGYyYTEwZDVjNDRkOTNlZmVhIiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJQcm94aW1pdHlQcml6ZS5TdWJtaXNzaW9uTG93ZXIuSEZyZWU2ODEyLmRlcml2YXRpb25fb3JkZXJfaXRlcmF0ZV95dWtvbl8zN2RlYjIzYWY3MjQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

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

/-- (i) Iterated: `ord (Dᵏ f) ≥ ord f - k θ`. -/
theorem derivation_order_iterate_yukon_37deb23af724 (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s)
    (hsθ : s ≤ θ) (hπθ : v (D π) ≤ exp (θ - 1)) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) (k : ℕ) (f : L) :
    v ((⇑D)^[k] f) ≤ exp (k * θ) * v f  := by sorry
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
