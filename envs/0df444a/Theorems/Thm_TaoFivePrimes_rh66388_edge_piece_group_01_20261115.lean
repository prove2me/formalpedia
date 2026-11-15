-- Prove2me | Theorems.Thm_TaoFivePrimes_rh66388_edge_piece_group_01_20261115
-- name    : TaoFivePrimes.rh66388_edge_piece_group_01_20261115
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-14T19:45:50.995387+00:00
-- url     : https://prove2.me/theorems/91cbf5e8-2a85-4311-9d75-8bbb4a8323ae
-- title:
--   Certified contour pieces 5 through 9 at height 66388
-- statement:
--   The exact finite arithmetic check succeeds for each encoded horizontal contour piece with index at least 5 and less than 10, at height 66388. This finite certificate is a component of the zero-count proof.
-- source:
--   Finite contour certificates for the Dusart Table 1 row-23 formalization; P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388EdgeFullCandidate

theorem TaoFivePrimes.rh66388_edge_piece_group_01_20261115 (j : ℕ) (hlo : 5 ≤ j) (hhi : j < 10) : H11K.pieceJ RH66388Edge.withBoxes j = true := by sorry
