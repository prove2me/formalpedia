-- Prove2me | Theorems.Thm_StableFees_UserGain_gain_le_spacing
-- name    : StableFees.UserGain.gain_le_spacing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:23.650451+00:00
-- url     : https://prove2.me/theorems/fdfda160-6380-41cb-be5e-a56a7c87410e
-- title:
--   Proof of Result 3, p. 22 — pointwise gain is bounded by the bid spacing
-- statement:
--   Let $2\le K\le m$, let $x\in[0,\bar V]^m$ be the truthful bids of the other active users, and let $v\in[0,\bar V]$. The best improvement over a truthful bid satisfies
--
--   $$0\le G_{K,\bar V}(v;x)\le V_{K-1}(x)-V_K(x),\qquad G_{K,\bar V}(v;x)>0\;\Longrightarrow\;v\ge V_K(x).$$
--
--   This is the pointwise bound that transfers the incentive question to the spacing of adjacent order statistics.
-- source:
--   Basu, Easley, O'Hara, Sirer, Towards a Functional Fee Market for Cryptocurrencies, arXiv:1901.06830v1, p. 22, proof of Result 3

import Mathlib
import Definitions.Def_StableFees_UserGain_Model

namespace StableFees.UserGain

theorem gain_le_spacing (K m : ℕ) (hK : 2 ≤ K) (hm : K ≤ m)
    (Vbar v : ℝ) (hVbar : 0 < Vbar) (hv : v ∈ Set.Icc 0 Vbar)
    (x : Fin m → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 Vbar) :
    0 ≤ gain K Vbar v x ∧
    gain K Vbar v x ≤ kthHighest x (K - 1) - kthHighest x K ∧
    (0 < gain K Vbar v x → kthHighest x K ≤ v) := by sorry

end StableFees.UserGain
