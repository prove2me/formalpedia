-- Prove2me | Theorems.Thm_ShiShallow_ccz_phase_exponent_eq
-- name    : ShiShallow.ccz_phase_exponent_eq
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T03:48:58.249223+00:00
-- url     : https://prove2.me/theorems/5ff75d79-ee34-4adf-ac47-728285df3d42
-- title:
--   The 7-T CCZ phase-exponent identity
-- statement:
--   An identity between complex numbers indexed by three Boolean variables.
--
--   Writing omega = exp(i*pi/4), a primitive eighth root of unity, the claim is that
--
--     omega ^ (a + b + c + 7*(a xor b) + 7*(b xor c) + 7*(a xor c) + (a xor b xor c))
--
--   (each Bool read as 0 or 1) equals -1 exactly when a, b and c are all true, and 1 otherwise -- that is, it equals (-1) raised to the AND of the three bits.
--
--   WHAT IT IS FOR. This is the phase bookkeeping underlying the standard seven-T decomposition of the CCZ gate. One omega factor appears per T-type gate: a T on each of the three wires, a T-adjoint on each of the three pairwise parities, and a T on the triple parity. The adjoint gates contribute omega^7 rather than omega^(-1), which is legitimate because omega has order 8; that is also why the gate set used here, which provides T but no adjoint constructor, can express the circuit at all.
--
--   Verification is by exhaustion over the eight inputs, and the arithmetic is worth recording: the all-true case gives exponent 4, and omega^4 = -1; every other case gives exponent 16 or 0, both multiples of 8, hence omega to that power is 1. So the identity is not an approximation or a phase convention -- it is exact on the nose.
--
--   WHAT THIS IS NOT. It constructs no circuit and proves no circuit identity. Nothing here refers to Instr, runLayered, cnotState or apply1, and no claim is made that any particular sequence of gates realises this product of phases -- that is a separate statement about circuit semantics. The gate set in this development is H, S, T, X, CNOT with no universality theorem, and no unitarity or normalisation is assumed anywhere.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem ccz_phase_exponent_eq (a b c : Bool) :
    Complex.exp (Complex.I * Real.pi / 4) ^
        ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
          + 7 * (if xor a b then 1 else 0) + 7 * (if xor b c then 1 else 0)
          + 7 * (if xor a c then 1 else 0) + (if xor a (xor b c) then 1 else 0))
      = if (a && b && c) then (-1 : ℂ) else 1 := by
  sorry

end ShiShallow
