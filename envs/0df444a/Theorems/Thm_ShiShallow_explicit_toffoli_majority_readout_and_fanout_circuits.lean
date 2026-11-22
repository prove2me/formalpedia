-- Prove2me | Theorems.Thm_ShiShallow_explicit_toffoli_majority_readout_and_fanout_circuits
-- name    : ShiShallow.explicit_toffoli_majority_readout_and_fanout_circuits
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-18T06:20:29.990056+00:00
-- url     : https://prove2.me/theorems/0b2801e7-bd34-4044-8e76-75003bbc7e2a
-- title:
--   Explicit gate lists for the Toffoli, the majority readout and the fan-out
-- statement:
--   The Toffoli gate, the three-copy majority readout and the fan-out layer are exhibited as LITERAL gate lists over the gate set, each pinned by an equation rather than merely asserted to exist. The Toffoli is a Hadamard conjugation of the standard T and controlled-not ladder for the doubly controlled phase, one gate per layer, so its depth is 37 by construction and each layer is well formed because it holds a single gate; the readout is three such Toffolis at the three pairs of copy output wires, of depth 111; the fan-out is a single layer of controlled-nots. Existing results give these circuits only up to their action, which leaves their gate lists undetermined and so leaves the encoding of a circuit built from them undetermined too. Pinning them as terms is what makes that encoding a definite string. The Toffoli's action is checked at concrete basis strings, the target flipping exactly when both controls are set.

import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_apply1_tMat_eq_phase
import Theorems.Thm_ShiShallow_cnot_conj_phase_map
import Theorems.Thm_ShiShallow_phase_composition
import Theorems.Thm_ShiShallow_ccz_phase_exponent_eq
import Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self
import Theorems.Thm_ShiShallow_runLayered_append_action_readout

set_option autoImplicit false

namespace ShiShallow

theorem explicit_toffoli_majority_readout_and_fanout_circuits {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (w1 w2 w3 s : Fin N) (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) (n : ℕ) :
    (∃ tof : Layered N,
        tof =
          [
           [Instr.h r], [Instr.t p], [Instr.t q], [Instr.t r], [Instr.cnot p q hpq], [Instr.t q],
           [Instr.t q], [Instr.t q], [Instr.t q], [Instr.t q], [Instr.t q], [Instr.t q],
           [Instr.cnot p q hpq], [Instr.cnot q r hqr], [Instr.t r], [Instr.t r], [Instr.t r],
           [Instr.t r], [Instr.t r], [Instr.t r], [Instr.t r], [Instr.cnot q r hqr],
           [Instr.cnot p r hpr], [Instr.t r], [Instr.t r], [Instr.t r], [Instr.t r], [Instr.t r],
           [Instr.t r], [Instr.t r], [Instr.cnot p r hpr], [Instr.cnot p r hpr],
           [Instr.cnot q r hqr], [Instr.t r], [Instr.cnot q r hqr], [Instr.cnot p r hpr],
           [Instr.h r]
          ]
        ∧ (∀ ψ : QState N, runLayered tof ψ
            = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
        ∧ (∀ l ∈ tof, LayerOk l)
        ∧ depth tof = 37)
    ∧ (∃ read : Layered N,
        read =
          [
           [Instr.h s], [Instr.t w1], [Instr.t w2], [Instr.t s], [Instr.cnot w1 w2 h12],
           [Instr.t w2], [Instr.t w2], [Instr.t w2], [Instr.t w2], [Instr.t w2], [Instr.t w2],
           [Instr.t w2], [Instr.cnot w1 w2 h12], [Instr.cnot w2 s h2s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.cnot w2 s h2s],
           [Instr.cnot w1 s h1s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.cnot w1 s h1s], [Instr.cnot w1 s h1s],
           [Instr.cnot w2 s h2s], [Instr.t s], [Instr.cnot w2 s h2s], [Instr.cnot w1 s h1s],
           [Instr.h s]
          ] ++
          [
           [Instr.h s], [Instr.t w2], [Instr.t w3], [Instr.t s], [Instr.cnot w2 w3 h23],
           [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3],
           [Instr.t w3], [Instr.cnot w2 w3 h23], [Instr.cnot w3 s h3s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.cnot w3 s h3s],
           [Instr.cnot w2 s h2s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.cnot w2 s h2s], [Instr.cnot w2 s h2s],
           [Instr.cnot w3 s h3s], [Instr.t s], [Instr.cnot w3 s h3s], [Instr.cnot w2 s h2s],
           [Instr.h s]
          ] ++
          [
           [Instr.h s], [Instr.t w1], [Instr.t w3], [Instr.t s], [Instr.cnot w1 w3 h13],
           [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3],
           [Instr.t w3], [Instr.cnot w1 w3 h13], [Instr.cnot w3 s h3s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.cnot w3 s h3s],
           [Instr.cnot w1 s h1s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.cnot w1 s h1s], [Instr.cnot w1 s h1s],
           [Instr.cnot w3 s h3s], [Instr.t s], [Instr.cnot w3 s h3s], [Instr.cnot w1 s h1s],
           [Instr.h s]
          ]
        ∧ (∀ ψ : QState N, runLayered read ψ
            = fun x => ψ (Function.update x s
                (xor (x s) (xor (xor (x w1 && x w2) (x w2 && x w3)) (x w1 && x w3)))))
        ∧ (∀ l ∈ read, LayerOk l)
        ∧ depth read = 111)
    ∧ (∃ fan : Layered (n + n),
        fan =
          [(List.finRange n).map (fun j : Fin n =>
            Instr.cnot (Fin.castAdd n j) (Fin.natAdd n j)
              (fun hEq => absurd (congrArg Fin.val hEq)
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right n (j : ℕ))))))]
        ∧ (∀ φ : QState (n + n), runLayered fan φ
            = fun y => φ (Fin.addCases
                (fun i : Fin n => y (Fin.castAdd n i))
                (fun j : Fin n => xor (y (Fin.natAdd n j)) (y (Fin.castAdd n j)))))
        ∧ (∀ l ∈ fan, LayerOk l)
        ∧ depth fan = 1)
    ∧ (∃ c3 : Layered 3,
        c3 =
          [
           [Instr.h 2], [Instr.t (0 : Fin 3)], [Instr.t 1], [Instr.t 2],
           [Instr.cnot (0 : Fin 3) 1 (by decide)], [Instr.t 1], [Instr.t 1], [Instr.t 1],
           [Instr.t 1], [Instr.t 1], [Instr.t 1], [Instr.t 1],
           [Instr.cnot (0 : Fin 3) 1 (by decide)], [Instr.cnot 1 2 (by decide)], [Instr.t 2],
           [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2],
           [Instr.cnot 1 2 (by decide)], [Instr.cnot (0 : Fin 3) 2 (by decide)], [Instr.t 2],
           [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2],
           [Instr.cnot (0 : Fin 3) 2 (by decide)], [Instr.cnot (0 : Fin 3) 2 (by decide)],
           [Instr.cnot 1 2 (by decide)], [Instr.t 2], [Instr.cnot 1 2 (by decide)],
           [Instr.cnot (0 : Fin 3) 2 (by decide)], [Instr.h 2]
          ]
        ∧ ∀ ψ : QState 3,
            runLayered c3 ψ ![true, true, false] = ψ ![true, true, true]
            ∧ runLayered c3 ψ ![true, true, true] = ψ ![true, true, false]
            ∧ runLayered c3 ψ ![true, false, false] = ψ ![true, false, false]
            ∧ runLayered c3 ψ ![false, true, true] = ψ ![false, true, true]) := by
  sorry

end ShiShallow
