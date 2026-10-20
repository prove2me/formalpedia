-- Prove2me | Theorems.Thm_PermanentRollout_blockIncidence_ringKrullDim_le_of_power_reductions
-- name    : PermanentRollout.blockIncidence_ringKrullDim_le_of_power_reductions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/f7a6eb12-0187-413e-b792-e541140d1af9
-- title:
--   PermanentRollout.blockIncidence_ringKrullDim_le_of_power_reductions
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.blockIncidence_ringKrullDim_le_of_power_reductions
    {b t s d : ℕ} (hd : 3 ≤ d)
    (remainder : BlockIncidenceColumn b t s →
      MvPolynomial (BlockIncidenceColumn b t s)
        (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ))
    (hdegree : ∀ coordinate, (remainder coordinate).totalDegree < d - 1)
    (hrel :
      letI := blockIncidenceBaseAlgebra b t s d
      ∀ coordinate : BlockIncidenceColumn b t s,
        (Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2))) ^ (d - 1) =
        MvPolynomial.aeval
          (fun row : BlockIncidenceColumn b t s =>
            Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
              (MvPolynomial.X (row.1, Sum.inr row.2)))
          (remainder coordinate)) :
    ringKrullDim (BlockIncidenceCoordinateRing b t s d) ≤
      ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by sorry
