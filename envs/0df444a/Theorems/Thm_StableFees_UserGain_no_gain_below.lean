-- Prove2me | Theorems.Thm_StableFees_UserGain_no_gain_below
-- name    : StableFees.UserGain.no_gain_below
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:26.684398+00:00
-- url     : https://prove2.me/theorems/bc348b5d-41dc-4efe-a14a-30fe02bd6abd
-- title:
--   Proof of Result 3, p. 22 — a value below the Kth other bid cannot gain
-- statement:
--   Let $2\le K\le m$, let $x\in[0,\bar V]^m$ be the truthful bids of the other active users, and let $v\in[0,\bar V]$. If $v<V_K(x)$, truthful bidding loses and no admissible strategic bid has positive payoff:
--
--   $$u_K(v,v;x)=0,\qquad u_K(v,b;x)\le 0\quad(b\in[0,\bar V]).$$
--
--   The claim removes values below the inclusion threshold from the region where a deviation can help.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 22, proof of Result 3

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

namespace StableFees.UserGain

theorem no_gain_below (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v : ℝ) (hv : v ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar)
    (hbelow : v < kthHighest x K) :
    payoff K v v x = 0 ∧
    ∀ b ∈ Set.Icc 0 Vbar, payoff K v b x ≤ 0 := by sorry

end StableFees.UserGain
