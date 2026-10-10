-- Prove2me | Theorems.Thm_PriceQualityService_Surplus_proposition_5
-- name    : PriceQualityService.Surplus.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:18:58.35207+00:00
-- url     : https://prove2.me/theorems/3487f76d-747d-4f98-8a09-5a90999e80cb
-- title:
--   Proposition 5: consumer surplus rises with each decision the firm controls
-- statement:
--   Under the MNL model, consider a firm with products $i\in\mathcal N$, production costs $c_iq_i^2$ with $c_i>0$, service costs $t_i(a_i-b_iq_i)$ and service durations restricted to $[t_s,t_l]$ with $t_s\le t_l$. Fix pre-determined qualities $\mathbf q\in\mathbb R^N$ and durations $\mathbf t\in[t_s,t_l]^N$. Let
--
--   1. $\mathbf p^\dagger$ be **any** optimal solution of the price-only problem $\max_{\mathbf p}\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$;
--   2. $(\mathbf p^\ddagger,\mathbf t^\ddagger)$ be **any** optimal solution of the price-and-service problem $\max_{\mathbf p,\ \mathbf t'\in[t_s,t_l]^N}\Pi(\mathbf p,\mathbf q,\mathbf t';\mathcal N)$ at the same qualities;
--   3. $(\mathbf p^*,\mathbf q^*,\mathbf t^*)$ be **any** optimal solution of the joint problem (4) $\max_{\mathbf p,\mathbf q',\ \mathbf t'\in[t_s,t_l]^N}\Pi(\mathbf p,\mathbf q',\mathbf t';\mathcal N)$.
--
--   With consumer surplus $\mathrm{CS}(\mathbf p,\mathbf q,\mathbf t)=\log\big(1+\sum_{i\in\mathcal N}\exp(\alpha_iq_i-p_i+t_is_i)\big)$,
--   $$
--   \mathrm{CS}(\mathbf p^\dagger,\mathbf q,\mathbf t)\le\mathrm{CS}(\mathbf p^\ddagger,\mathbf q,\mathbf t^\ddagger)\le\mathrm{CS}(\mathbf p^*,\mathbf q^*,\mathbf t^*).
--   $$
--
--   Giving the firm more decisions cannot hurt the firm; the proposition shows that it does not hurt consumers either, a "win–win" in the paper's words: under MNL demand the extra profit comes from serving more consumers rather than from extracting more surplus from each.
--
--   **Formalization Note** "Higher" is read weakly ($\le$): equality occurs, for instance when the pre-determined $\mathbf q,\mathbf t$ are already jointly optimal. The statement quantifies over all maximizers; their existence is not part of the proposition. Qualities range over $\mathbb R$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 13 (PDF p. 13), Proposition 5; proof in Online Supplement pp. 1–2 (PDF pp. 34–35)

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Problems
import Definitions.Def_PriceQualityService_Surplus_ConsumerSurplus

namespace PriceQualityService.Surplus

open Finset

/-- Proposition 5, Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 13: consumer surplus
is (weakly) higher when the firm decides prices, qualities and service durations than when it
decides prices and service durations, which in turn gives (weakly) higher consumer surplus than
when it decides prices only.

Fix pre-determined qualities `q ∈ ℝ^N` and durations `t ∈ [t_s, t_l]^N`. For **every** maximizer
`p†` of the price-only problem at `(q, t)`, **every** maximizer `(p‡, t‡)` of the price-and-service
problem at the same `q`, and **every** maximizer `(p*, q*, t*)` of the joint problem (4),
`CS(p†, q, t) ⩽ CS(p‡, q, t‡) ⩽ CS(p*, q*, t*)`, where
`CS(p, q, t) = log(1 + ∑_i exp(α_i q_i − p_i + t_i s_i))`. -/
theorem proposition_5 {N : ℕ} (α a b c s : Fin N → ℝ) (ts tl : ℝ)
    (hc : ∀ i, 0 < c i) (hts : ts ≤ tl)
    (q t : Fin N → ℝ) (ht : ∀ i, t i ∈ Set.Icc ts tl)
    (pDag : Fin N → ℝ) (hDag : IsPriceOptimal α a b c s q t pDag)
    (pDdag tDdag : Fin N → ℝ) (hDdag : IsPriceServiceOptimal α a b c s ts tl q pDdag tDdag)
    (pStar qStar tStar : Fin N → ℝ) (hStar : IsJointOptimal α a b c s ts tl pStar qStar tStar) :
    consumerSurplus α s pDag q t ≤ consumerSurplus α s pDdag q tDdag ∧
      consumerSurplus α s pDdag q tDdag ≤ consumerSurplus α s pStar qStar tStar := by sorry

end PriceQualityService.Surplus
