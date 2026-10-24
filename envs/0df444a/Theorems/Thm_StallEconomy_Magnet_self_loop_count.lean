-- Prove2me | Theorems.Thm_StallEconomy_Magnet_self_loop_count
-- name    : StallEconomy.Magnet.self_loop_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:22.396989+00:00
-- url     : https://prove2.me/theorems/9e4f0646-d55c-430b-ab4b-d9a0a1ef3c77
-- title:
--   Proof of Theorem 1, Case I (IX), p. 48 — self-loop count for a type-1 rendezvous
-- statement:
--   If the current and next rendezvous coincide at a type-1 location $z_d\in\mathcal I_1$, the customers that keep the stall there are precisely the points of the small diamond $\mathcal I(z_d)$. Hence
--   $$
--   |\mathcal A(z_d,z_d)|=(2h+1)^2.
--   $$
--
--   This is the self-loop contribution in the paper's Case I column count.
--
--   **Formalization Note** The type-1 condition is essential: at a type-2 point, a rotated arrow can also return the stall to its origin.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 48, proof of Theorem 1, Case I (IX)

import Mathlib
import Definitions.Def_StallEconomy_Magnet_Setting

namespace StallEconomy.Magnet

theorem self_loop_count (k h : ℕ) (hkh : 2 * h ≤ k)
    (zd : ℤ × ℤ) (hzd : zd ∈ type1 k h) :
    (A k h zd zd).card = (2 * h + 1) ^ 2 := by sorry

end StallEconomy.Magnet
