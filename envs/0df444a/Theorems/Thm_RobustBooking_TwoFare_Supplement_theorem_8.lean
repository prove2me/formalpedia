-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_Supplement_theorem_8
-- name    : RobustBooking.TwoFare.Supplement.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T04:47:25.19074+00:00
-- url     : https://prove2.me/theorems/12458817-91d4-416b-8c28-00d448d351be
-- title:
--   Theorem 8 — discrete bid-price control: under (20) the order quantity policy based on P_ρ is at least ρ(1 − 1/(ρ(ρn + 1)))-competitive
-- statement:
--   Let $0<f_{\min}<f_{\max}$ and $r=f_{\min}/f_{\max}$. Consider the discrete bid-price problem with integer capacity $n$: unit orders with fares in $[f_{\min},f_{\max}]$, each accepted whole or rejected, at most $n$ accepted. Let $\rho$ be a desired performance level with
--   $$0<\rho<\frac{1}{1-\ln r},$$
--   and suppose the capacity satisfies (20),
--   $$n\ \ge\ \max\Big\{\frac{1}{1-\rho},\ \frac1\rho\,G^{(-1)}\big(r^{-\rho/(1-\rho)}\big)\Big\},$$
--   where $G(x)=(1+1/x)^x$ and $G^{(-1)}$ is its inverse. Then the order quantity control policy based on $P_\rho$ of (18)–(19) has competitive ratio at least
--   $$\rho\Big(1-\frac{1}{\rho(\rho n+1)}\Big):$$
--   on every instance $I$ with fares in $[f_{\min},f_{\max}]$, its revenue $v'(I)$ is at least this number times the offline optimum $v^*(I)$.
--
--   This is the discrete counterpart of Theorem 7; as $n$ grows the bound approaches the continuous guarantee $1/(1-\ln r)$ when $\rho$ is taken close to it. The bound can be negative; the paper notes this for small values of $r$.
--
--   **Formalization Note** The statement is the per-instance inequality $\rho(1-1/(\rho(\rho n+1)))\,v^*(I)\le v'(I)$ for every admissible instance, which is equivalent to the competitive ratio being at least the bound (instances with $v^*(I)=0$ are empty and satisfy it trivially). The bound is kept as printed, without positivity or clipping. $G^{(-1)}$ is `Ginv`, the supremum of $\{x>0: G(x)\le a\}$; under the hypotheses its argument $r^{-\rho/(1-\rho)}$ lies in $(1,e)$, where this is the true inverse.
--
--   Differences from the source:
--   - encoding: "the competitive ratio … is at least (21)" → (21)·v*(I) ≤ v′(I) for every instance with fares in [f_min, f_max]; reason: equivalent to the infimum of v′/v* over instances with v* > 0 being at least (21), and instances with v* = 0 are empty.
--   - encoding: G^(−1) → Ginv a = sup {x > 0 : G(x) ≤ a}; reason: equals G^(−1)(a) for 1 ≤ a < e, and the argument r^(−ρ/(1−ρ)) lies in (1, e) whenever 0 < ρ < 1/(1 − ln r).
--   - reading: "the discrete bid-price control problem" → n is a natural number and an instance is a finite list of unit orders, each with a real fare in [f_min, f_max]; reason: pp. 952 and 956: integer capacity in units, each request proposes a fare in that range and is one order with x_i ∈ {0,1}.
--   - encoding: "x_{k+1} = 0 if O_{k+1} < P(q̂), otherwise sup{α ∈ {0,1}: P(α + q̂) ⩽ O_{k+1}}" → accept iff q̂ < n, P_ρ(q̂) ≤ O and P_ρ(q̂ + 1) ≤ O; reason: this evaluates the supremum over {0,1}; q̂ < n is the capacity of p. 952, which is implicit on p. 956, where P is defined only for q ≤ n.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 961, Theorem 8, Eqs. (20)–(21), with P_ρ from p. 960, Eqs. (18)–(19), and the policy A′_θ of p. 956

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteBidPrice

namespace RobustBooking.TwoFare.Supplement

/-- Theorem 8 (Ball–Queyranne 2009, p. 961). Let `0 < f_min < f_max`, `r = f_min / f_max`, and let
`ρ` satisfy `0 < ρ < 1 / (1 - ln r)`. If the integer capacity `n` satisfies (20),
`n ≥ max {1 / (1 - ρ), (1/ρ) G^(-1)(r^(-ρ/(1-ρ)))}`, then on every instance of unit orders with
fares in `[f_min, f_max]` the discrete order quantity control policy based on `P_ρ` earns at least
`ρ (1 - 1 / (ρ (ρ n + 1)))` times the optimal offline revenue, i.e. its competitive ratio is at
least (21). -/
theorem theorem_8 (fmin fmax ρ : ℝ) (n : ℕ) (hfmin : 0 < fmin) (hfmax : fmin < fmax)
    (hρ : 0 < ρ) (hρr : ρ < 1 / (1 - Real.log (fmin / fmax)))
    (h20 : max (1 / (1 - ρ)) ((1 / ρ) * Ginv ((fmin / fmax) ^ (-(ρ / (1 - ρ))))) ≤ (n : ℝ))
    (I : List ℝ) (hI : ∀ O ∈ I, fmin ≤ O ∧ O ≤ fmax) :
    ρ * (1 - 1 / (ρ * (ρ * n + 1))) * bpOpt n I ≤ bpRevenue n (orderQtyPolicy fmin ρ n) I := by sorry

end RobustBooking.TwoFare.Supplement
