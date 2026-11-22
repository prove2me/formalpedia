-- Prove2me | Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_06_20261122
-- name    : TaoFivePrimes.rh67156_edge_piece_group_06_20261122
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-21T22:16:10.436564+00:00
-- url     : https://prove2.me/theorems/6105c282-2fd2-4ed8-b843-7eed1fd81b37
-- title:
--   Certified contour pieces 30 through 34 at height 67156
-- statement:
--   The exact finite arithmetic check succeeds for each encoded horizontal contour piece with index at least 30 and less than 35, at height 67156. This finite certificate is a component of the zero-count proof.
-- source:
--   Finite contour certificates for the Dusart Table 1 row-23 formalization; P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeFullCandidate

theorem TaoFivePrimes.rh67156_edge_piece_group_06_20261122 (j : ℕ) (hlo : 30 ≤ j) (hhi : j < 35) : H11K.pieceJ RH67156Edge.withBoxes j = true := by sorry
