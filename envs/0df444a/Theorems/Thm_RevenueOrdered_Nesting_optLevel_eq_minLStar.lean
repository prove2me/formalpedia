-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_optLevel_eq_minLStar
-- name    : RevenueOrdered.Nesting.optLevel_eq_minLStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:12.83241+00:00
-- url     : https://prove2.me/theorems/1acb0fed-19ff-4e4b-87f7-ce8ac1629da8
-- title:
--   Eqs. (17)–(18) — ℓ∗_t(q) = min 𝓛∗(−∆𝒥_{t−1}(q))
-- statement:
--   Consider the revenue-ordered multi-period dynamic program of §5 under a regular discrete choice model $\mathcal P$ with positive revenues $r$. For every $t\ge 1$ periods remaining and every $q\ge 1$ units left, the optimal revenue-ordered index $\ell^*_t(q)=\min\{\ell\in[k]:\mathcal J_t(q,\ell)=\mathcal J_t(q)\}$ satisfies
--   $$
--   \ell^*_t(q)=\min\mathcal L^*\bigl(-\Delta\mathcal J_{t-1}(q)\bigr),
--   $$
--   where $\mathcal L^*(\delta)$ is the set of indices of optimal revenue-ordered assortments when $\delta$ is added to every revenue. Equation (17) of the paper is the same identity at $q-1$ in place of $q$ (for $q\ge 2$).
--
--   In words: the largest optimal offer set at a stage of the dynamic program is the largest optimal revenue-ordered assortment of the single-period problem in which the marginal value of capacity is subtracted from every revenue.
--
--   **Formalization Note** The statement is written with $t+1$ and $t$ in place of the paper's $t$ and $t-1$ ($t\ge 1$), which avoids natural-number subtraction.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 36, Appendix B, Equations (17) and (18)

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_LStar
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

namespace RevenueOrdered.Nesting

/-- Equation (18), and (17) as its instance at `q − 1` (Berbeglia–Joret, arXiv:1606.01371v3,
App. B, p. 36): with `t + 1 ≥ 1` periods and `q ≥ 1` units remaining,
`ℓ∗_{t+1}(q) = min 𝓛∗(−∆𝒥_t(q))`.
(The paper writes the period indices as `t` and `t − 1`, with `t ≥ 1`.) -/
theorem optLevel_eq_minLStar {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsRegular P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (hq : 1 ≤ q) :
    optLevel P r (t + 1) q = minLStar P r (-marginalValue P r t q) := by sorry

end RevenueOrdered.Nesting
