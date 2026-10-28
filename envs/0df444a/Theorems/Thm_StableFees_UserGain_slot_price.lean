-- Prove2me | Theorems.Thm_StableFees_UserGain_slot_price
-- name    : StableFees.UserGain.slot_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:21.712098+00:00
-- url     : https://prove2.me/theorems/125c3d35-7b50-4d1c-a086-9352d9160463
-- title:
--   Proof of Result 3, p. 22 — the bidder or an opponent sets the uniform price
-- statement:
--   Let $2\le K\le m$, with $x\in[0,\bar V]^m$ and $v,b\in[0,\bar V]$, and suppose $v\ge V_K(x)$. Conditional on the considered bidder winning ($V_K(x)<b$), the payoff is
--
--   $$u_K(v,b;x)=\begin{cases}v-V_{K-1}(x),&V_{K-1}(x)\le b,\\v-b,&b<V_{K-1}(x).\end{cases}$$
--
--   This records which bid is the lowest included fee in the two cases. A bid tied at $V_K$ loses under the chosen tie rule.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 22, proof of Result 3

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

namespace StableFees.UserGain

theorem slot_price (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v b : ℝ) (hv : v ∈ Set.Icc 0 Vbar) (hb : b ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar)
    (hvalue : kthHighest x K ≤ v) :
    (kthHighest x K < b → kthHighest x (K - 1) ≤ b →
      payoff K v b x = v - kthHighest x (K - 1)) ∧
    (kthHighest x K < b → b < kthHighest x (K - 1) →
      payoff K v b x = v - b) := by sorry

end StableFees.UserGain
