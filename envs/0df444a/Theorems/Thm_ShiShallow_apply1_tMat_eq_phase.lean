-- Prove2me | Theorems.Thm_ShiShallow_apply1_tMat_eq_phase
-- name    : ShiShallow.apply1_tMat_eq_phase
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T04:23:59.850407+00:00
-- url     : https://prove2.me/theorems/a5e1f5b8-7dc0-4a4f-b529-bdb65d1ab180
-- title:
--   A T gate acts as a pointwise phase, with no sum
-- statement:
--   Because tMat is diagonal, a T gate acts as multiplication by a phase depending on a single bit, with no summation.
--
--   apply1 tMat i psi is a priori a sum over the two Boolean values of wire i. The term whose index differs from x i has coefficient zero, since tMat is diagonal; and in the surviving term the update rewrites wire i to the value it already holds, so the index reduces to x itself. What is left is multiplication by exp(i*pi/4) when bit i of x is true and by 1 otherwise.
--   WHY THIS IS THE RIGHT FOUNDATION. A CCZ circuit over this gate set uses only T and its adjoint (both diagonal) together with CNOT (a pure reindexing of the index). With a lemma of this shape, a diagonal-gate application needs NO sum at all, so the action of an entire such circuit on an ARBITRARY state -- not merely on a basis vector -- is a product of phase factors composed with a permutation of the index set. That turns the circuit argument into bookkeeping rather than analysis, and it is the reason CCZ is reachable here while a Hadamard-containing decomposition is not.
--
--   H IS EXCLUDED, AND NECESSARILY SO. hMat is not diagonal -- its entries are minus the inverse square root of two when both indices are true and plus that value otherwise -- so no analogous "acts as a pointwise phase" statement is true for H, and none is claimed. This is exactly the contrast that makes a Toffoli decomposition harder than a CCZ one: Hadamard genuinely creates superpositions.
--
--   SCOPE. This is a SINGLE-GATE statement. It says nothing about sequencing, composition, or any multi-gate circuit identity. The gate set is H, S, T, X, CNOT and NO universality theorem is imported or proved. No unitarity is assumed of the gate matrix and no normalisation of the state: psi is an arbitrary function to the complex numbers.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem apply1_tMat_eq_phase {n : ℕ} (i : Fin n) (ψ : QState n) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  sorry

end ShiShallow
