-- Prove2me | Theorems.Thm_PriceQualityService_Surplus_proposition_8
-- name    : PriceQualityService.Surplus.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:19:33.975957+00:00
-- url     : https://prove2.me/theorems/a1447ba2-522d-4041-b597-f00a57be102d
-- title:
--   Proposition 8: with fixed qualities, offer every product, use extreme durations and equal markups
-- statement:
--   Qualities $\mathbf q$ are pre-determined, and the firm chooses an offer set $S\subseteq\mathcal N$, prices $\mathbf p\in\mathbb R^N$ and service durations $\mathbf t\in[t_s,t_l]^N$ to maximize the offer-set profit $\Pi_S(\mathbf p,\mathbf q,\mathbf t)$ (problem (10)). Assume $c_i>0$, $t_s\le t_l$, and, for every product with $b_i>0$, the model's quality range $q_i\le a_i/b_i$. Then there are an optimal profit $r^*$ and durations $t^*_i\in\{t_s,t_l\}$ given by
--
--   - (a) if $b_i=0$: $t^*_i=t_l$ when $a_i\le s_i$, otherwise $t^*_i=t_s$;
--   - (b) if $b_i>0$: $t^*_i=t_l$ when $(a_i-s_i)/b_i\le q_i\le a_i/b_i$, otherwise $t^*_i=t_s$;
--   - (c) if $b_i<0$: $t^*_i=t_s$ when $q_i\ge(a_i-s_i)/b_i$, otherwise $t^*_i=t_l$,
--
--   such that
--
--   1. $r^*$ is the unique real solution of
--   $$
--   r=\sum_{i\in\mathcal N}\exp\big(\alpha_iq_i-c_iq_i^2+t^*_i(s_i-(a_i-b_iq_i))-r-1\big);
--   $$
--   2. offering all products, $S=\mathcal N$, with durations $\mathbf t^*$ and prices $p^*_i=1+r^*+c_iq_i^2+t^*_i(a_i-b_iq_i)$ is optimal for (10), with profit $r^*$;
--   3. every optimal $(S,\mathbf p,\mathbf t)$ offers all products ($S=\mathcal N$), earns $r^*$, has $p_i=1+r^*+c_iq_i^2+t_i(a_i-b_iq_i)$ for every $i$, and $r^*$ solves the equation above with $\mathbf t$ in place of $\mathbf t^*$.
--
--   With qualities fixed the optimal durations are extreme and the markups are product-invariant, as in Theorem 1; this problem without the offer-set choice is the price-and-service problem of Proposition 5.
--
--   **Formalization Note** The hypothesis $q_i\le a_i/b_i$ for $b_i>0$ is the model's quality range (p. 8, "it varies in $[0,a_i/b_i)$"); without it the printed "otherwise, $t_s$" in (b) can be wrong, since $q_i>a_i/b_i$ makes the service cost negative. At the boundary of each case condition both durations are optimal, so "the optimal service duration is …" is read as "an optimal service duration is …": the case rule is stated for one optimum, while the universal clause 3 covers every optimum. Problem (10) is printed with $\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$ where the offer set $S$ is meant.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 21 (PDF p. 21), Proposition 8; problem (10), p. 20; proof in Online Supplement pp. 7–8 (PDF pp. 40–41)

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Problems

namespace PriceQualityService.Surplus

open Finset

/-- Proposition 8, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 21: the
manufacturer's short-term problem (10) with pre-determined qualities `q`.

There are an optimal profit `r*` and durations `t* ∈ [t_s, t_l]^N` following the case rule
(a) `b_i = 0`: `t_l` if `a_i ≤ s_i`, otherwise `t_s`;
(b) `b_i > 0`: `t_l` if `(a_i − s_i)/b_i ≤ q_i ≤ a_i/b_i`, otherwise `t_s`;
(c) `b_i < 0`: `t_s` if `q_i ≥ (a_i − s_i)/b_i`, otherwise `t_l`,
such that `r*` is the unique real root of
`r = ∑_i exp(α_i q_i − c_i q_i² + t*_i(s_i − (a_i − b_i q_i)) − r − 1)`, offering all products at
durations `t*` and prices `p*_i = 1 + r* + c_i q_i² + t*_i(a_i − b_i q_i)` is optimal for (10) with
profit `r*`, and every optimal `(S, p, t)` offers all products (`S = 𝒩`), earns `r*`, has every
price equal to `1 + r* + c_i q_i² + t_i(a_i − b_i q_i)`, and `r*` solves the equation at its `t`.

Added hypothesis (model range, p. 8): `q_i ≤ a_i/b_i` whenever `b_i > 0`. -/
theorem proposition_8 {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)
    (hc : ∀ i, 0 < c i) (hts : ts ≤ tl) (q : Fin N → ℝ)
    (hq : ∀ i, 0 < b i → q i ≤ a i / b i) :
    ∃ (rStar : ℝ) (tStar : Fin N → ℝ),
      (∀ i, b i = 0 →
        (a i ≤ s i → tStar i = tl) ∧ (¬ a i ≤ s i → tStar i = ts)) ∧
      (∀ i, 0 < b i →
        ((a i - s i) / b i ≤ q i ∧ q i ≤ a i / b i → tStar i = tl) ∧
        (¬ ((a i - s i) / b i ≤ q i ∧ q i ≤ a i / b i) → tStar i = ts)) ∧
      (∀ i, b i < 0 →
        (q i ≥ (a i - s i) / b i → tStar i = ts) ∧ (¬ q i ≥ (a i - s i) / b i → tStar i = tl)) ∧
      rStar = ∑ i, Real.exp (α i * q i - c i * q i ^ 2
          + tStar i * (s i - (a i - b i * q i)) - rStar - 1) ∧
      (∀ r : ℝ, r = ∑ i, Real.exp (α i * q i - c i * q i ^ 2
          + tStar i * (s i - (a i - b i * q i)) - r - 1) → r = rStar) ∧
      IsOfferOptimal α a b c s ts tl q Finset.univ
        (fun i => 1 + rStar + c i * q i ^ 2 + tStar i * (a i - b i * q i)) tStar ∧
      offerProfit α a b c s Finset.univ
        (fun i => 1 + rStar + c i * q i ^ 2 + tStar i * (a i - b i * q i)) q tStar = rStar ∧
      ∀ (S : Finset (Fin N)) (p t : Fin N → ℝ), IsOfferOptimal α a b c s ts tl q S p t →
        S = Finset.univ ∧ offerProfit α a b c s S p q t = rStar ∧
        (∀ i, p i = 1 + rStar + c i * q i ^ 2 + t i * (a i - b i * q i)) ∧
        rStar = ∑ i, Real.exp (α i * q i - c i * q i ^ 2
          + t i * (s i - (a i - b i * q i)) - rStar - 1) := by sorry

end PriceQualityService.Surplus
