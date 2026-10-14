-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_upper_bound_step
-- name    : PerishablePricing.Bounds.upper_bound_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:57.616783+00:00
-- url     : https://prove2.me/theorems/94a209d0-5989-4708-a8c2-bbbfa8c650e5
-- title:
--   Proof of Theorem 3, p. 295 — G_t(s, s′_l, d) − G_t(s, s_l, d) ≤ Π_t(s′_l, d) − Π_t(s_l, d)
-- statement:
--   Consider the backlogging model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3, §4 and §6.1. For every period, every state $s\in\mathcal S$, every expected demand $d\in\mathcal D$ and every pair of order-up-to levels $s'_l>s_l\ge s_{l-1}$,
--
--   $$G_t(s,s'_l,d)-G_t(s,s_l,d)\ \le\ \Pi_t(s'_l,d)-\Pi_t(s_l,d).$$
--
--   Ordering up to a higher level gains at most the myopic gain, because the continuation value is nonincreasing in the inventory carried over. This gives the upper bound $s_{lt}(s,d)\le\bar S_t(d)\vee s_{l-1}$ of Theorem 3.
--
--   **Formalization Note.** The page derives the display from "$G_t(s,s_l,d)=\Pi_t(s_l,d)+\gamma\mathbb E[f_{t+1}(\tilde s)]$", which omits the term $-\tilde\theta\,\mathbb E[(s_1-d_t)^+]$ (see the decomposition at $a=d_t\vee s_1$); that term does not depend on $s_l$, so the difference inequality, which is what is stated here, is unaffected. Time is counted in periods to go.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, proof of Theorem 3, p. 295, first display

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Myopic

namespace PerishablePricing.Bounds

/-- Proof of Theorem 3 (p. 295), upper bound, first display (zero lead time, backlogging,
`θ ≥ h⁺/(1 − γ)`): for two inventory decisions `s′_l > s_l ≥ s_{l−1}`,
`G_t(s, s′_l, d) − G_t(s, s_l, d) ≤ Π_t(s′_l, d) − Π_t(s_l, d)`
for every state `s ∈ 𝒮` and expected demand `d ∈ 𝒟`. -/
theorem upper_bound_step (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi)
    (sl sl' : ℝ) (hsl : sLast s ≤ sl) (hlt : sl < sl') :
    M.G (M.f n) s sl' d - M.G (M.f n) s sl d ≤ M.Pi sl' d - M.Pi sl d := by sorry

end PerishablePricing.Bounds
