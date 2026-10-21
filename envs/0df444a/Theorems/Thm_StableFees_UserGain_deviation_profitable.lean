-- Prove2me | Theorems.Thm_StableFees_UserGain_deviation_profitable
-- name    : StableFees.UserGain.deviation_profitable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:19.201892+00:00
-- url     : https://prove2.me/theorems/d37f35f1-bad4-4869-98d9-ad3b39cdccea
-- title:
--   Proof of Result 3, p. 21 — a bid between the two thresholds improves payoff
-- statement:
--   Let $2\le K\le m$, let $x\in[0,\bar V]^m$ be the truthful bids of the other active users, and let $v,b\in[0,\bar V]$. If $V_K(x)<b<V_{K-1}(x)<v$, then
--
--   $$u_K(v,b;x)=v-b>v-V_{K-1}(x)=u_K(v,v;x).$$
--
--   This explicit profitable deviation establishes the failure of dominant strategy truthfulness whenever the adjacent other bids are distinct.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 21, proof of Result 3

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

namespace StableFees.UserGain

theorem deviation_profitable (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v b : ℝ) (hv : v ∈ Set.Icc 0 Vbar) (hb : b ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar)
    (hbelow : kthHighest x K < b)
    (hbetween : b < kthHighest x (K - 1))
    (habove : kthHighest x (K - 1) < v) :
    payoff K v b x = v - b ∧
    payoff K v v x = v - kthHighest x (K - 1) ∧
    payoff K v v x < payoff K v b x := by sorry

end StableFees.UserGain
