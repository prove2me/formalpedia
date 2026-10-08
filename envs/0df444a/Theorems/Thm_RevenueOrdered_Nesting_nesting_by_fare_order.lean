-- Prove2me | Theorems.Thm_RevenueOrdered_Nesting_nesting_by_fare_order
-- name    : RevenueOrdered.Nesting.nesting_by_fare_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:32:44.605524+00:00
-- url     : https://prove2.me/theorems/320ee775-2dce-48d4-bbfb-d5cfbb946072
-- title:
--   Theorem 5.1 — ℓ∗_t(q) is non-increasing in capacity left and non-decreasing in time left
-- statement:
--   Let $\mathcal P$ be a regular discrete choice model on a finite nonempty set of products $\mathcal C$, and $r:\mathcal C\to\mathbb R_{>0}$ a revenue function with distinct values $r_1<\cdots<r_k$ and revenue-ordered assortments $S_\ell=\{x:r(x)\ge r_\ell\}$. In the multi-period model with one customer per period, let $\mathcal J_t(q,\ell)$ and $\mathcal J_t(q)=\max_{\ell\in[k]}\mathcal J_t(q,\ell)$ be the values of the revenue-ordered dynamic program with $t$ periods remaining and $q$ units left, and
--   $$
--   \ell^*_t(q)=\min\{\ell\in[k]:\mathcal J_t(q,\ell)=\mathcal J_t(q)\}.
--   $$
--   Then for every $t\ge 1$ and $q\ge 1$:
--
--   1. $\ell^*_t(q)\le\ell^*_t(q-1)$ if $q\ge 2$, and
--   2. $\ell^*_t(q)\ge\ell^*_{t-1}(q)$ if $t\ge 2$.
--
--   Since a smaller index means a larger offer set, the largest optimal revenue-ordered assortment grows (weakly) with the inventory left and shrinks (weakly) as more periods remain. This is the nesting-by-fare-order property, which Rusmevichientong et al. proved for mixtures of multinomial logit models; the theorem extends it to every regular discrete choice model.
--
--   **Formalization Note** The paper states the theorem for $t\in[T]$ and $q\in[Q]$; the horizon $T$ and capacity $Q$ only bound $t$ and $q$ and play no other role, so the statement is made for all $t,q\ge 1$. The index $\ell$ is the paper's 1-based index in $[k]$. The paper's prose on p. 4 and p. 36 describes the time direction the other way round; the statement follows the theorem's bullets.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 25, Theorem 5.1

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_DynamicProgram

namespace RevenueOrdered.Nesting

/-- Theorem 5.1 (Berbeglia–Joret, arXiv:1606.01371v3, p. 25): under a regular discrete choice
model with positive revenues, for every `t ≥ 1` periods remaining and `q ≥ 1` units remaining,
* `ℓ∗_t(q) ≤ ℓ∗_t(q − 1)` if `q ≥ 2`, and
* `ℓ∗_t(q) ≥ ℓ∗_{t−1}(q)` if `t ≥ 2`.
The horizon `T` and capacity `Q` of the paper only bound `t ∈ [T]` and `q ∈ [Q]`; the
statement is made for all `t, q ≥ 1`. -/
theorem nesting_by_fare_order {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
    {P : C → Finset C → ℝ} {r : C → ℝ} (hP : IsRegular P) (hr : ∀ x, 0 < r x)
    (t q : ℕ) (ht : 1 ≤ t) (hq : 1 ≤ q) :
    (2 ≤ q → optLevel P r t q ≤ optLevel P r t (q - 1)) ∧
      (2 ≤ t → optLevel P r (t - 1) q ≤ optLevel P r t q) := by sorry

end RevenueOrdered.Nesting
