-- Prove2me | Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_01_20261122
-- name    : TaoFivePrimes.rh67156_edge_piece_group_01_20261122
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-21T22:16:10.241809+00:00
-- url     : https://prove2.me/theorems/a3f3e214-90eb-4bf0-9abe-ec5520071b33
-- title:
--   Certified contour pieces 5 through 9 at height 67156
-- statement:
--   The exact finite arithmetic check succeeds for each encoded horizontal contour piece with index at least 5 and less than 10, at height 67156. This finite certificate is a component of the zero-count proof.
-- source:
--   Finite contour certificates for the Dusart Table 1 row-23 formalization; P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeFullCandidate

theorem TaoFivePrimes.rh67156_edge_piece_group_01_20261122 (j : ℕ) (hlo : 5 ≤ j) (hhi : j < 10) : H11K.pieceJ RH67156Edge.withBoxes j = true := by sorry
