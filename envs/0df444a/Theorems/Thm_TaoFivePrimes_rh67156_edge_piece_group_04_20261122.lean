-- Prove2me | Theorems.Thm_TaoFivePrimes_rh67156_edge_piece_group_04_20261122
-- name    : TaoFivePrimes.rh67156_edge_piece_group_04_20261122
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-21T22:15:47.297071+00:00
-- url     : https://prove2.me/theorems/2ba83897-980a-40aa-87c6-1b68c2a24676
-- title:
--   Certified contour pieces 20 through 24 at height 67156
-- statement:
--   The exact finite arithmetic check succeeds for each encoded horizontal contour piece with index at least 20 and less than 25, at height 67156. This finite certificate is a component of the zero-count proof.
-- source:
--   Finite contour certificates for the Dusart Table 1 row-23 formalization; P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH67156EdgeFullCandidate

theorem TaoFivePrimes.rh67156_edge_piece_group_04_20261122 (j : ℕ) (hlo : 20 ≤ j) (hhi : j < 25) : H11K.pieceJ RH67156Edge.withBoxes j = true := by sorry
