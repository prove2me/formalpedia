-- Prove2me | Theorems.Thm_PermanentRollout_deletedCoordinateEsymmPolynomial_eq_alternating
-- name    : PermanentRollout.deletedCoordinateEsymmPolynomial_eq_alternating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/a23fafab-f958-4343-8866-db5e937b1d89
-- title:
--   PermanentRollout.deletedCoordinateEsymmPolynomial_eq_alternating
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.deletedCoordinateEsymmPolynomial_eq_alternating
    (t : ℕ) (i : Fin t) (q : ℕ) :
    deletedCoordinateEsymmPolynomial t q i =
      ∑ j ∈ Finset.range (q + 1),
        (-MvPolynomial.X i) ^ (q - j) *
          partitionFiberCoordinateEsymmPolynomial t j := by sorry
