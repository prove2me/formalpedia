-- Prove2me | Theorems.Thm_ShiShallow_acceptOperator_isHermitian
-- name    : ShiShallow.acceptOperator_isHermitian
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T22:25:20.089862+00:00
-- url     : https://prove2.me/theorems/19a228de-a06c-45dd-92f8-78db98f98026
-- title:
--   The acceptance operator of a circuit is Hermitian
-- statement:
--   Conjugating the output projector by any operator yields a Hermitian operator. Taking A to be the matrix of a circuit, this says the acceptance operator of that circuit is Hermitian, which is what licenses applying the spectral theorem and the variational principle to it.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem acceptOperator_isHermitian {n : ℕ} (A : Op n) (out : Fin n) :
    (star A * projOut out * A).IsHermitian := by
  sorry

end ShiShallow
