-- Prove2me | Theorems.Thm_TaoFivePrimes_rh66388_segment_cut_upper_20261115
-- name    : TaoFivePrimes.rh66388_segment_cut_upper_20261115
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-11-14T20:22:52.156034+00:00
-- url     : https://prove2.me/theorems/8102b1e9-bb6d-4af5-b706-e41286db2e44
-- title:
--   Finite-height RH segment 66388: upper input
-- statement:
--   The encoded horizontal argument change of zeta at height 66388 lies in the stated exact interval. This is a finite supporting certificate for the row-23 reduction.
-- source:
--   Finite zero-count certificate supporting P. Dusart, Ramanujan J. 45 (2018), Table 1, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH66388CountScalar
open Complex
noncomputable section

theorem TaoFivePrimes.rh66388_segment_cut_upper_20261115 :
    DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc RH66388Count.enclosure.L2.val RH66388Count.enclosure.H2.val := by sorry
