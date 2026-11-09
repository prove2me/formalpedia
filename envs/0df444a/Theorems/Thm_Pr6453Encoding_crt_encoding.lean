-- Prove2me | Theorems.Thm_Pr6453Encoding_crt_encoding
-- name    : Pr6453Encoding.crt_encoding
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T22:37:51.757305+00:00
-- url     : https://prove2.me/theorems/4697dd2e-cf62-4ac7-b80c-c77552c82cab
-- title:
--   PR #6453: the CRT encoding computes multiplication
-- statement:
--   The CRT encoding of a product, stated explicitly. Encode a polynomial by its values at the points of a finite set S, multiply the encodings pointwise, decode by interpolation: the result is the product, provided the product's degree is below the number of points. The ingredients are that evaluation is multiplicative and additive, and that below that bound the evaluations determine a polynomial.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (module block).

import Mathlib

set_option autoImplicit false

namespace Pr6453Encoding

theorem crt_encoding {R : Type*} [CommRing R] [IsDomain R] {S : Finset R} (p q r : Polynomial R)
    (hpq : (p * q).natDegree < S.card) (hr : r.natDegree < S.card)
    (h : ∀ x ∈ S, Polynomial.eval x r = Polynomial.eval x p * Polynomial.eval x q) :
    r = p * q := by
  sorry

end Pr6453Encoding
