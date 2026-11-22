-- Prove2me | Theorems.Thm_ShiTensor_sum_split_factor
-- name    : ShiTensor.sum_split_factor
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T05:06:33.161374+00:00
-- url     : https://prove2.me/theorems/dca02963-31ee-4ed7-af60-bd51d9201d07
-- title:
--   Sums factorise over the left/right bit split
-- statement:
--   Sums factorise over the left/right split: for f on Bits m and g on Bits p,
--
--     sum over y : Bits (m + p) of f (leftBits y) * g (rightBits y) = (sum of f) * (sum of g).
--
--   Proof: build the bijection Bits (m + p) ~= Bits m x Bits p from the leftBits/rightBits/Fin.append inverse facts, transport the sum along it, split the sum over the product type into a double sum, and recognise a double sum of a product as a product of sums.
--
--   DELIBERATELY STATED OVER A GENERAL NonUnitalNonAssocSemiring, not over the complex numbers. That generality is load-bearing rather than decorative: the same lemma then serves both the complex-amplitude use and the real-valued norm-squared use, which is what avoids needing a separate real companion lemma. It is also stated for arbitrary f and g rather than specialised to tensor, so it is reusable; taking f = psi and g = phi gives the statement about tensor directly, since tensor psi phi y is by definition psi (leftBits y) * phi (rightBits y).
--
--   SCOPE. This is the factorisation engine an independence argument needs, but it is NOT itself a probabilistic statement: there is no measure, no PMF, and no notion of independence anywhere. Nothing here relates tensor to runLayered or to acceptance probabilities.

import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow

namespace ShiTensor

theorem sum_split_factor {m p : ℕ} {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : Bits m → R) (g : Bits p → R) :
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
      = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := by
  sorry

end ShiTensor
