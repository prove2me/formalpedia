-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_proposition1_myopic_vs_strategic
-- name    : ReferencePricing.Myopic.proposition1_myopic_vs_strategic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:47:49.483732+00:00
-- url     : https://prove2.me/theorems/b0abdec7-d321-406d-9e29-066568852e75
-- title:
--   Proposition 1 (Myopic vs. Strategic Firm) — the myopic firm underprices, pointwise and along paths, and its prices converge monotonically to one price
-- statement:
--   Let $P = [0, \bar p]$ with $\bar p > 0$, memory $\alpha \in [0, 1)$ and discount factor $\beta \in (0, 1)$. Let demand be $D(p, r) = d(p) + R(r - p, r)$ with $R(0, r) = 0$, $d$ differentiable, and Assumptions 1, 2 and 3 in force; profit is $\Pi(p, r) = p\,D(p,r)$. Let $\tilde p$ be the myopic price and $p^*$ the optimal price (largest maximizers of $\Pi(\cdot, r)$ and of $W(\cdot, r)$ over $P$), and for an initial reference price $r_0$ let $p^M_t$ and $p^*_t$ be the myopic and optimal price paths, each along its own reference-price path. Then:
--
--   1. for every reference price $r \in P$, the myopic firm underprices: $p^*(r) \ge \tilde p(r)$;
--   2. for every $r_0 \in P$ and every $t \ge 0$: $p^M_t \le p^*_t$;
--   3. there is a single price $p^{M*} \in P$ such that for every $r_0 \in P$ the myopic price path is monotone (increasing or decreasing) and
--   $$\lim_{t \to \infty} p^M_t = p^{M*}.$$
--
--   Ignoring the effect of current prices on future reference prices leads a firm to price systematically too low, while its own prices settle monotonically at one level independent of where consumers' expectations started.
--
--   **Formalization Note.** Assumptions 2 and 3 are the standing assumptions of §§4.1–4.3 and are hypotheses of the whole statement, although the first two claims use only Assumption 1 and 3(c). Differentiability of $d$ is added (Assumption 3(b) refers to $\pi'$; Lean's `deriv` is $0$ off differentiability). "A unique constant price" is encoded with the price quantified before the initial reference price, so the limit is the same for every $r_0$. "Less than" is $\le$, as the displayed inequality $p^M_t \le p^*_t$ shows.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 418, Proposition 1

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_optPrice
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

open Filter Topology

namespace ReferencePricing.Myopic

/-- Proposition 1 (Myopic vs. Strategic Firm), p. 418, under the standing assumptions of §4:
(i) for every reference price `r ∈ P`, `p*(r) ≥ p̃(r)`;
(ii) for every initial reference price `r₀ ∈ P` and every `t`, `p^M_t ≤ p*_t`;
(iii) there is one price `p^{M*} ∈ P` such that every myopic price path, from every `r₀ ∈ P`,
is monotone (increasing or decreasing) and converges to `p^{M*}`. -/
theorem proposition1_myopic_vs_strategic (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    (∀ r ∈ Set.Icc (0 : ℝ) pbar,
        myopicPrice (profit d R) pbar r ≤ optPrice (profit d R) α β pbar r) ∧
      (∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, ∀ t : ℕ,
        myopicPricePath (profit d R) α pbar r₀ t ≤ pricePath (profit d R) α β pbar r₀ t) ∧
      (∃ pM ∈ Set.Icc (0 : ℝ) pbar, ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        (Monotone (myopicPricePath (profit d R) α pbar r₀) ∨
            Antitone (myopicPricePath (profit d R) α pbar r₀)) ∧
          Tendsto (myopicPricePath (profit d R) α pbar r₀) atTop (𝓝 pM)) := by sorry

end ReferencePricing.Myopic
