-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlockAlpha_eq_squareZeroCoefficient
-- name    : PermanentRollout.sourceBlockAlpha_eq_squareZeroCoefficient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/63331d27-ffcc-49d6-b47d-ef3678a42377
-- title:
--   PermanentRollout.sourceBlockAlpha_eq_squareZeroCoefficient
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceBlockAlpha_eq_squareZeroCoefficient
    {r d : ℕ} (U : Matrix (Fin r) (Fin (r - d)) ℂ)
    (omitted : Finset (Fin r))
    (homitted : omitted.card = d) :
    sourceBlockAlpha r d U omitted =
      squareZeroCoefficient r
        ((Finset.univ : Finset (Fin r)) \ omitted)
        (Ideal.Quotient.mk (squareZeroIdeal r)
          (columnLinearFormProduct U)) := by sorry
