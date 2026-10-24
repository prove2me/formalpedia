-- Prove2me | Theorems.Thm_StallEconomy_Magnet_column_count_type2
-- name    : StallEconomy.Magnet.column_count_type2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:54.814219+00:00
-- url     : https://prove2.me/theorems/9e7021f9-e9f1-4c7e-8c85-cc89345c84d5
-- title:
--   Proof of Theorem 1, Case II, pp. 48–49 — unit column count at a type-2 rendezvous
-- statement:
--   Fix a type-2 rendezvous $z_d\in\mathcal I_0\setminus\mathcal I_1$. The boundary corrections in the magnet rule leave the total incoming customer count unchanged:
--   $$
--   \sum_{z_o\in\mathcal I_0}|\mathcal A(z_o,z_d)|=(k+1)^2.
--   $$
--
--   This is the boundary case needed for every column of the transition matrix to sum to one.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), pp. 48–49, proof of Theorem 1, Case II

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem column_count_type2 (k h : ℕ) (hkh : 2 * h ≤ k)
    (zd : ℤ × ℤ) (hzd : zd ∈ inner k h) (hn : zd ∉ type1 k h) :
    ∑ zo : inner k h, (A k h zo.1 zd).card = (k + 1) ^ 2 := by sorry

end StallEconomy.Magnet
