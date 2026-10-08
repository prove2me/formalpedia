-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_jVal_eq_max_shifted
-- name    : RevenueOrdered.Nesting.jVal_eq_max_shifted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:16.965358+00:00
-- url     : https://prove2.me/theorems/e559c291-3de7-40db-b6c4-18067a67e123
-- title:
--   Eq. (16) — 𝒥_t(q) = max_ℓ ∑_{x∈S_ℓ} 𝒫(x, S_ℓ)(r(x) − ∆𝒥_{t−1}(q)) + 𝒥_{t−1}(q)
-- statement:
--   Consider the revenue-ordered multi-period dynamic program of §5 under a regular discrete choice model $\mathcal P$ with positive revenues $r$, with values $\mathcal J_t(q)$ and marginal values $\Delta\mathcal J_t(q)=\mathcal J_t(q)-\mathcal J_t(q-1)$. For every $t\ge 1$ periods remaining and every $q\ge 1$ units left,
--   $$
--   \mathcal J_t(q)=\max_{\ell\in[k]}\Bigl\{\sum_{x\in S_\ell}\mathcal P(x,S_\ell)\bigl(r(x)-\Delta\mathcal J_{t-1}(q)\bigr)\Bigr\}+\mathcal J_{t-1}(q).
--   $$
--
--   The identity rewrites one stage of the dynamic program as a single-period revenue-ordered assortment problem in which the marginal value of capacity is subtracted from every revenue. It uses $\mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S)$.
--
--   **Formalization Note** The statement is written with $t+1$ and $t$ in place of the paper's $t$ and $t-1$ ($t\ge 1$), which avoids natural-number subtraction. The maximum is `Finset.sup'` over $[k]$ of `shiftedRevenue` at $\delta=-\Delta\mathcal J_t(q)$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 36, Appendix B, Equation (16)

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_LStar
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

namespace RevenueOrdered.Nesting

/-- Equation (16) (Berbeglia–Joret, arXiv:1606.01371v3, App. B, p. 36): with `t + 1 ≥ 1`
periods and `q ≥ 1` units remaining,
`𝒥_{t+1}(q) = max_{ℓ ∈ [k]} ∑_{x ∈ S_ℓ} 𝒫(x, S_ℓ)(r(x) − ∆𝒥_t(q)) + 𝒥_t(q)`.
(The paper writes the period indices as `t` and `t − 1`, with `t ≥ 1`.) -/
theorem jVal_eq_max_shifted {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsRegular P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    jVal P r (t + 1) q =
      (levels r).sup' (levels_nonempty r) (shiftedRevenue P r (-marginalValue P r t q)) +
        jVal P r t q := by sorry

end RevenueOrdered.Nesting
