-- Prove2me | Theorems.Thm_ShiShallow_exists_fanout_embedded_pullback
-- name    : ShiShallow.exists_fanout_embedded_pullback
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T19:52:43.611329+00:00
-- url     : https://prove2.me/theorems/233a4caa-b222-465a-a144-9714b2a07c4f
-- title:
--   A fan-out placed at arbitrary wires of a larger register, as an explicit single well-formed layer
-- statement:
--   Given an injection of a doubled block of wires into a larger register, there is a circuit on the larger register that exclusive-ors each wire of the first half of the block into the corresponding wire of the second half, leaves every wire outside the second half untouched, consists of a single well-formed layer, and acts on states by substitution along an explicit map of basis strings.
--
--   The placement is arbitrary: the two halves of the block may sit anywhere in the register and need not be adjacent. This is what distinguishes the statement from one about a fan-out on its own register together with a relabelling, which is not available: relabelling results transport only states that vanish outside the relabelled wires, or require the relabelling to be a permutation of the whole register, or require the circuit to sit inside a single tensor factor, and a fan-out that straddles two regions of a register satisfies none of these.
--
--   That the action is a substitution on basis strings, rather than a general linear map, is recorded explicitly because it is what allows the effect on a state of known support to be computed. The intended use is a verifier that must supply the same input to several independent copies of a subcircuit, where the copies' input wires are held in the ancilla region and begin in the zero state.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

open ShiShallow

theorem exists_fanout_embedded_pullback (n N : ℕ) (g : Fin (n + n) → Fin N) (hg : Function.Injective g) :
    ∃ (c : Layered N) (u : Bits N → Bits N),
      (∀ Φ : QState N, runLayered c Φ = fun Y => Φ (u Y))
      ∧ (∀ (Y : Bits N) (j : Fin n), u Y (g (Fin.natAdd n j))
            = xor (Y (g (Fin.natAdd n j))) (Y (g (Fin.castAdd n j))))
      ∧ (∀ (Y : Bits N) (k : Fin N), (∀ j : Fin n, g (Fin.natAdd n j) ≠ k) → u Y k = Y k)
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 1 := by
  sorry

end ShiShallow
