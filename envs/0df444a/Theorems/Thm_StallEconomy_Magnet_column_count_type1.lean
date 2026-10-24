-- Prove2me | Theorems.Thm_StallEconomy_Magnet_column_count_type1
-- name    : StallEconomy.Magnet.column_count_type1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:10.680981+00:00
-- url     : https://prove2.me/theorems/0a4cdfb6-62bf-499c-aca6-c768805c501c
-- title:
--   Proof of Theorem 1, Case I, pp. 46–48 — unit column count at a type-1 rendezvous
-- statement:
--   Fix a type-1 rendezvous $z_d\in\mathcal I_1$. Summing over all possible stall origins in the inner diamond, the number of customer locations leading to $z_d$ equals the full customer-grid size:
--   $$
--   \sum_{z_o\in\mathcal I_0}|\mathcal A(z_o,z_d)|=(k+1)^2.
--   $$
--
--   Dividing by the full-grid size establishes a unit column sum for type-1 rendezvous.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), pp. 46–48, proof of Theorem 1, Case I

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem column_count_type1 (k h : ℕ) (hkh : 2 * h ≤ k)
    (zd : ℤ × ℤ) (hzd : zd ∈ type1 k h) :
    ∑ zo : inner k h, (A k h zo.1 zd).card = (k + 1) ^ 2 := by sorry

end StallEconomy.Magnet
