-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_theorem_3
-- name    : PerishablePricing.Bounds.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:00.093791+00:00
-- url     : https://prove2.me/theorems/83204147-d7ba-406f-84d5-f2a3bae1fca5
-- title:
--   Theorem 3 (Bounds), p. 295 — S̲_t(d) ∨ s_{l−1} ≤ s_lt(s, d) ≤ S̄_t(d) ∨ s_{l−1}
-- statement:
--   Consider the backlogging perishable inventory–pricing model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3 (nonnegative unit costs, $0\le\gamma\le1$, $P$ strictly decreasing on $\mathcal D$, $P(d)d$ continuous and concave on $\mathcal D$, zero-mean i.i.d. noise supported in $[A,B]$ with $A\le 0\le B$, $\underline d+A\ge 0$), the assumption $c\le h^-/(1-\gamma)$ of §4, and the assumption $\theta\ge h^+/(1-\gamma)$ of §6.1 (with $\gamma<1$).
--
--   Fix a period $t$, a state $s\in\mathcal S$ and an expected demand level $d\in\mathcal D$. Let $s_{lt}(s,d)$ be the largest maximizer of $s_l\mapsto G_t(s,s_l,d)$ over $s_l\ge s_{l-1}$, and let $\bar S_t(d)$ and $\underline S_t(d)$ be the largest maximizers of $\Pi_t(\cdot,d)$ and $\tilde\Pi_t(\cdot,d)$ over $s_l\ge 0$. Then
--
--   $$\underline S_t(d)\vee s_{l-1}\ \le\ s_{lt}(s,d)\ \le\ \bar S_t(d)\vee s_{l-1}.$$
--
--   The optimal order-up-to level of the $l$-dimensional dynamic program is thus bracketed by the solutions of two one-dimensional myopic problems. Since the data are stationary, the bounds do not depend on $t$ (Remark 6: "the bounds are in fact independent of time").
--
--   **Formalization Note.** Only the backlogging case is stated; the paper's Theorem 3 also covers the lost-sales case, whose concavity rests on Theorem 2, which is not part of this mission. The paper assumes that the planning horizon starts with zero inventory; that assumption constrains no object of the statement ($f_t$, $G_t$ and $s_{lt}(s,d)$ are defined by the recursion at every state), so the conclusion is stated for every $s\in\mathcal S$. The optimal decisions are the *largest* maximizers, taken as hypotheses (they are assumed to exist); with an arbitrary maximizer the upper bound can fail when $\Pi_t(\cdot,d)$ is flat. $\theta\ge h^+/(1-\gamma)$ is stated as $h^+\le(1-\gamma)\theta$ with $\gamma<1$, and $c\le h^-/(1-\gamma)$ as $(1-\gamma)c\le h^-$. Time is counted in periods to go: $G_t$ is `G (f n)` for any `n`. $\underline S_t(d)$ is defined through $\tilde\Pi_t$ exactly as printed on p. 294, with the weight $\gamma^{l-1}\tilde\theta$. The display in the paper's proof of the lower bound does not hold for every pair $s'_l>s_l\ge s_{l-1}$ when $h^+>\gamma c$. The theorem itself is stated as printed.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Theorem 3, p. 295 (backlogging case), with §6 (zero lead time) and §6.1 (θ ≥ h⁺/(1 − γ)), p. 294

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Myopic

namespace PerishablePricing.Bounds

/-- Theorem 3 (Bounds, p. 295), backlogging case, zero lead time, `θ ≥ h⁺/(1 − γ)`: for every
period (every number of periods to go `n`), every state `s ∈ 𝒮` and every expected demand
`d ∈ 𝒟`, the largest optimal order-up-to level `s_lt(s, d)` (the largest maximizer of
`s_l ↦ G_t(s, s_l, d)` over `s_l ≥ s_{l−1}`) satisfies
`S̲_t(d) ∨ s_{l−1} ≤ s_lt(s, d) ≤ S̄_t(d) ∨ s_{l−1}`,
where `S̄_t(d)` and `S̲_t(d)` are the largest maximizers of `Π_t(·, d)` and `Π̃_t(·, d)` over
`s_l ≥ 0`. -/
theorem theorem_3 (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi)
    (S Sbar Sund : ℝ)
    (hS : IsLargestMaxOn (fun sl => M.G (M.f n) s sl d) (Set.Ici (sLast s)) S)
    (hSbar : IsLargestMaxOn (fun sl => M.Pi sl d) (Set.Ici 0) Sbar)
    (hSund : IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund) :
    max Sund (sLast s) ≤ S ∧ S ≤ max Sbar (sLast s) := by sorry

end PerishablePricing.Bounds
