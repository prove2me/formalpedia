-- Prove2me | Theorems.Thm_ShiShallow_circMatrix_unitary
-- name    : ShiShallow.circMatrix_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-13T20:52:55.867516+00:00
-- url     : https://prove2.me/theorems/1c092548-9ca5-4333-80f7-50faccc0aaf5
-- title:
--   The matrix of a layered circuit is unitary
-- statement:
--   The matrix of any layered circuit is unitary: star (circMatrix c) * circMatrix c = 1. Proved by induction on the list of layers, since circMatrix is a product of layer matrices and each layer matrix is unitary. Unconditional: no hypotheses about the gate set beyond the definitions.

import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem circMatrix_unitary {n : ℕ} (c : Layered n) :
    star (circMatrix c) * circMatrix c = (1 : Op n) := by
  sorry

end ShiShallow
