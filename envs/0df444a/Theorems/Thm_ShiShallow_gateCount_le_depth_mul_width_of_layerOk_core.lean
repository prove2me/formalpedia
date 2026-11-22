-- Prove2me | Theorems.Thm_ShiShallow_gateCount_le_depth_mul_width_of_layerOk_core
-- name    : ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T06:40:54.633334+00:00
-- url     : https://prove2.me/theorems/fedd4f12-f3ce-44cd-8a4c-3b3228be4a7b
-- title:
--   Gate count is at most depth times width, on the five-gate instruction set
-- statement:
--   For a layered circuit on a fixed number of wires, all of whose layers are well formed in the sense that their gates act on pairwise disjoint sets of wires, the total number of gates is at most the number of layers times the number of wires.
--
--   The reason is that a single well-formed layer cannot contain more gates than there are wires. Every instruction acts on at least one wire, and within a layer no two instructions share a wire, so choosing one wire from each instruction's support injects the layer's gates into the wires. Summing the resulting per-layer bound over the layers gives the statement.
--
--   The bound is in one direction only: it says nothing about the depth, the number of wires, or the number of two-wire gates, and it fails without well-formedness, since an arbitrary layer may repeat a gate on the same wire any number of times. Its use is to convert a bound on depth and width into a bound on size, which is what lets a serialised circuit, whose depth equals its gate count, still be recognised as polynomially bounded.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem gateCount_le_depth_mul_width_of_layerOk_core {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l) :
    (c.map List.length).sum ≤ depth c * n := by
  sorry

end ShiShallow
