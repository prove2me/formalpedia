-- Prove2me | Theorems.Thm_StallEconomy_Magnet_positive_transition
-- name    : StallEconomy.Magnet.positive_transition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:10.488181+00:00
-- url     : https://prove2.me/theorems/ae15374b-7ac4-4c52-be28-7bef2b5b454f
-- title:
--   Proof of Theorem 1 (II), p. 49 — every transition probability is positive
-- statement:
--   For every pair of inner-diamond locations $z_o,z_d\in\mathcal I_0$, at least one customer grid point sends the stall from $z_o$ to $z_d$ under the magnet rule:
--   $$
--   |\mathcal A(z_o,z_d)|>0.
--   $$
--
--   Since the denominator $(k+1)^2$ is positive, this is equivalent to $\mathbb P(z_o,z_d)>0$. Positivity supplies the irreducibility and ergodicity used in the paper's stationary-law argument.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 49, proof of Theorem 1 (II)

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem positive_transition (k h : ℕ) (hkh : 2 * h ≤ k)
    (zo zd : inner k h) :
    0 < (A k h zo.1 zd.1).card := by sorry

end StallEconomy.Magnet
