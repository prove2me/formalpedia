-- Prove2me | Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_02_20261115
-- name    : TaoFivePrimes.rh66388_edge_piece_group_02_20261115
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-14T19:46:15.893135+00:00
-- url     : https://prove2.me/theorems/a7198615-f4c9-4416-b572-c2f86d3c3228
-- title:
--   Certified contour pieces 10 through 14 at height 66388
-- statement:
--   The exact finite arithmetic check succeeds for each encoded horizontal contour piece with index at least 10 and less than 15, at height 66388. This finite certificate is a component of the zero-count proof.
-- source:
--   Finite contour certificates for the Dusart Table 1 row-23 formalization; P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeFullCandidate

theorem TaoFivePrimes.rh66388_edge_piece_group_02_20261115 (j : ℕ) (hlo : 10 ≤ j) (hhi : j < 15) : H11K.pieceJ RH66388Edge.withBoxes j = true := by sorry
