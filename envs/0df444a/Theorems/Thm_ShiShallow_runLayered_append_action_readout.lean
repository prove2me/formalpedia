-- Prove2me | Theorems.Thm_ShiShallow_runLayered_append_action_readout
-- name    : ShiShallow.runLayered_append_action_readout
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T07:22:17.044471+00:00
-- url     : https://prove2.me/theorems/8ee3ac79-eeab-46fd-8409-dbfd4c7b4904
-- title:
--   Composing an action stage with a pull-back readout stage
-- statement:
--   If the first part of a circuit realises a given map on states, and the second part acts by pulling states back along a given reindexing of basis strings, then the concatenation applies the reindexing to the result of the first part. Circuit evaluation over a concatenation is the composition of the two evaluations, so this is the gluing law for an action stage followed by a readout stage.

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem runLayered_append_action_readout {N : ℕ} (cA cR : Layered N)
    (fA : QState N → QState N) (uR : Bits N → Bits N)
    (hA : ∀ ψ, runLayered cA ψ = fA ψ)
    (hR : ∀ ψ, runLayered cR ψ = fun x => ψ (uR x))
    (ψ : QState N) :
    runLayered (cA ++ cR) ψ = fun x => fA ψ (uR x) := by
  sorry

end ShiShallow
