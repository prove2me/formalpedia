-- Prove2me | Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_02_20261122
-- name    : TaoFivePrimes.rh67156_edge_piece_group_02_20261122
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-21T22:16:21.040616+00:00
-- url     : https://prove2.me/theorems/4507eb60-0f58-46be-810d-7162ea6f26cb
-- title:
--   Certified contour pieces 10 through 14 at height 67156
-- statement:
--   The exact finite arithmetic check succeeds for each encoded horizontal contour piece with index at least 10 and less than 15, at height 67156. This finite certificate is a component of the zero-count proof.
-- source:
--   Finite contour certificates for the Dusart Table 1 row-23 formalization; P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeFullCandidate

theorem TaoFivePrimes.rh67156_edge_piece_group_02_20261122 (j : ℕ) (hlo : 10 ≤ j) (hhi : j < 15) : H11K.pieceJ RH67156Edge.withBoxes j = true := by sorry
