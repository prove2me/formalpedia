-- Prove2me | Theorems.Thm_ShiShallow_exists_majority_readout_at_wires_layerOk_depth
-- name    : ShiShallow.exists_majority_readout_at_wires_layerOk_depth
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T08:52:39.636362+00:00
-- url     : https://prove2.me/theorems/1fc1fb45-ef2f-414e-a087-152960386f3e
-- title:
--   The majority readout at any four wires, as an explicit well-formed circuit of depth one hundred and eleven
-- statement:
--   For any four distinct wires of a register, three of them read as inputs and one as a scratch wire, there is a circuit that exclusive-ors the majority of the three inputs into the scratch wire and leaves every other wire alone. The circuit has one hundred and eleven layers, each with a single gate, so every layer is well formed and the depth is exactly one hundred and eleven however large the register is.
--
--   The majority of three bits is the exclusive-or of the three pairwise conjunctions, so the circuit is three doubly-controlled negations sharing the scratch wire as target, one for each pair of inputs. Each of those is itself a thirty-seven layer circuit, since the available gate set has no doubly-controlled gate and no inverse phase gate, and the three cannot be run in parallel because they share the scratch wire.
--
--   As with its components, the depth and the well-formedness are asserted alongside the action, because an existence statement that fixes only what a circuit computes cannot support either: the witness is not recoverable from the statement, and both properties are demanded of any circuit family that is to be recognised as polynomially bounded. The count is independent of the register size, which is what allows the readout to be used as a fixed-cost component of a larger family.

import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_exists_toffoli_at_wires_layerOk_depth
import Theorems.Thm_ShiShallow_runLayered_append_action_readout

set_option autoImplicit false

namespace ShiShallow

theorem exists_majority_readout_at_wires_layerOk_depth {N : ℕ} (w1 w2 w3 s : Fin N)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) :
    ∃ c : Layered N,
      (∀ ψ : QState N, runLayered c ψ
          = fun x => ψ (Function.update x s
              (xor (x s) (xor (xor (x w1 && x w2) (x w2 && x w3)) (x w1 && x w3)))))
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 111 := by
  sorry

end ShiShallow
