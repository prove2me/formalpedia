-- Prove2me | Theorems.Thm_PermanentRollout_blockIncidence_adjoin_column_coordinates
-- name    : PermanentRollout.blockIncidence_adjoin_column_coordinates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/efab5c24-a3c5-456f-9780-f3ada5e4b4d3
-- title:
--   PermanentRollout.blockIncidence_adjoin_column_coordinates
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.blockIncidence_adjoin_column_coordinates
    (b t s d : ℕ) :
    letI := blockIncidenceBaseAlgebra b t s d
    Algebra.adjoin
      (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
      (Set.range fun coordinate : BlockIncidenceColumn b t s =>
        Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
          (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2))) =
      (⊤ : Subalgebra
        (MvPolynomial (BlockIncidenceBaseIndex b t s d) ℂ)
        (BlockIncidenceCoordinateRing b t s d)) := by sorry
