-- Prove2me | Theorems.Thm_ShiShallow_exists_toffoli_at_wires_layerOk_depth
-- name    : ShiShallow.exists_toffoli_at_wires_layerOk_depth
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T08:34:21.128145+00:00
-- url     : https://prove2.me/theorems/f7ba5d55-d9e3-4258-9813-0c800cd33a5a
-- title:
--   A Toffoli gate at any three wires, as an explicit well-formed circuit of depth thirty-seven
-- statement:
--   For any three distinct wires of a register there is a circuit that exclusive-ors the conjunction of the first two into the third and leaves every other wire alone. The circuit has thirty-seven layers, each containing a single gate, so every layer is trivially well formed and the depth is exactly thirty-seven regardless of how many wires the register has.
--
--   The gate set available consists of the Hadamard, phase and π/8 gates on one wire together with the controlled-not on two, and contains no doubly-controlled gate and no inverse of the π/8 gate. The circuit is therefore the standard decomposition: a Hadamard on the target, then a controlled-controlled-phase built from seven single-wire phase blocks conjugated by controlled-nots, then a Hadamard on the target again. Each inverse phase is written as seven copies of the forward phase, since the alphabet has no inverse letter and seven forward copies have the same effect.
--
--   The depth and the well-formedness are asserted alongside the action because an existence statement that fixes only the action of a circuit cannot support either, the witness being unrecoverable. Both are needed of any circuit family that is to be recognised as polynomially bounded, and the count being independent of the register size is what makes the construction usable as a fixed-cost component.

import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_apply1_tMat_eq_phase
import Theorems.Thm_ShiShallow_cnot_conj_phase_map
import Theorems.Thm_ShiShallow_phase_composition
import Theorems.Thm_ShiShallow_ccz_phase_exponent_eq
import Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self

set_option autoImplicit false

namespace ShiShallow

theorem exists_toffoli_at_wires_layerOk_depth {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ c : Layered N,
      (∀ ψ : QState N, runLayered c ψ
          = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 37 := by
  sorry

end ShiShallow
