-- Prove2me | Theorems.Thm_PriceQualityService_Uniform_theorem_3
-- name    : PriceQualityService.Uniform.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:35.489331+00:00
-- url     : https://prove2.me/theorems/9a9f8ff3-55ae-4445-977a-8e7c438607dc
-- title:
--   Theorem 3: an optimal uniform service duration is $t_s$ or $t_l$
-- statement:
--   Consider the joint price, quality and **uniform** service duration problem (7): the firm chooses prices $\mathbf p\in\mathbb R^N$, qualities $\mathbf q\in\mathbb R^N$ and one service duration $t\in[t_s,t_l]$ shared by all products ($t_i=t$ for every $i\in\mathcal N$), to maximize the total expected profit
--   $$
--   \max_{\mathbf p,\mathbf q,\,t\in[t_s,t_l]}\ \Pi\big(\mathbf p,\mathbf q,(t,\dots,t);\mathcal N\big)
--   $$
--   under the MNL model (2)–(3). Assume $c_i>0$ for every product and $t_s\le t_l$.
--
--   **Theorem 3.** The optimal uniform service duration is at one of the boundary points: there exist $t^*\in\{t_s,t_l\}$ and vectors $\mathbf p^*,\mathbf q^*$ such that
--   $$
--   \Pi\big(\mathbf p,\mathbf q,(t,\dots,t);\mathcal N\big)\le\Pi\big(\mathbf p^*,\mathbf q^*,(t^*,\dots,t^*);\mathcal N\big)
--   \quad\text{for all }t\in[t_s,t_l],\ \mathbf p,\mathbf q\in\mathbb R^N.
--   $$
--   In particular problem (7) has an optimal solution, and it can be taken with $t^*=t_s$ or $t^*=t_l$.
--
--   Even when all products must carry the same service duration, the firm should offer either the shortest or the longest one; the paper uses this benchmark to measure the value of service differentiation.
--
--   **Formalization Note** This is the existential reading of "the optimal uniform service duration is $t_s$ or $t_l$": when the optimal profit does not depend on $t$ (every $b_i=0$ and $a_i=s_i$) every duration is optimal, so the universal reading needs a non-degeneracy assumption and is a separate item. Existence of an optimum is part of the conclusion. Prices and qualities are unconstrained reals, as in the paper's first-order derivation.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 15, Theorem 3 (problem (7)); proof pp. 29–30

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model

namespace PriceQualityService.Uniform

/-- Theorem 3, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 15: in problem (7), the
joint price, quality and uniform service duration problem `max_{p,q,t} Π(p, q, t; 𝒩)` with
`t_i = t ∈ [t_s, t_l]` for every product, an optimal uniform duration is at a boundary point.
There are `τ ∈ {t_s, t_l}` and price and quality vectors `p*`, `q*` such that the profit at
`(p*, q*, τ)` is at least the profit of every `(p, q, t)` with `t ∈ [t_s, t_l]`. -/
theorem theorem_3 {N : ℕ} (α a b c s : Fin N → ℝ) (hc : ∀ i, 0 < c i) (ts tl : ℝ)
    (hts : ts ≤ tl) :
    ∃ τ : ℝ, (τ = ts ∨ τ = tl) ∧ ∃ pStar qStar : Fin N → ℝ,
      ∀ t ∈ Set.Icc ts tl, ∀ p q : Fin N → ℝ,
        PriceQualityService.Joint.profit α a b c s p q (fun _ => t) ≤ PriceQualityService.Joint.profit α a b c s pStar qStar (fun _ => τ) := by sorry

end PriceQualityService.Uniform
