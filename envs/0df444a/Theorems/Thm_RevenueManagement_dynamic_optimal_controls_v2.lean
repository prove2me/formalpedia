-- Prove2me | Theorems.Thm_RevenueManagement_dynamic_optimal_controls_v2
-- name    : RevenueManagement.dynamic_optimal_controls_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:04.966684+00:00
-- url     : https://prove2.me/theorems/76cf716f-5c45-4814-af01-e06de7e05b82
-- title:
--   Theorem 2.2: the dynamic model is optimally controlled by time-dependent nested protection levels (2.19), booking limits (2.20), or bid-price tables (2.18) — on the corrected `IsDynOptimal`
-- statement:
--   For the dynamic model (2.17) with an arrival model, prices $p_1\ge\dots\ge p_n\ge0$, capacity $C$ and a period $1\le t\le T$: the time-dependent protection levels are nested, $y_j^*(t)\le y_{j+1}^*(t)$; and for a class-$j$ request ($1\le j\le n$) with $1\le x\le C$ units remaining, each of the following accept/reject decisions maximizes $(p_j-\Delta V_{t+1}(x))\,u$ over $u\in\{0,1\}$: (i) accept iff $x>y_{j-1}^*(t)$, the protection levels (2.19); (ii) accept iff $C-x<b_j^*(t)$, the booking limits (2.20); (iii) accept iff $p_j\ge\pi_{t+1}(x)$, the bid prices (2.18).
--
--   **Formalization Note.** The statement is that of the retired milestone; what changed is the imported definition module. In the retired `Def_RevenueManagement_singleResource` the competitor $u'$ in `IsDynOptimal` was elaborated as a real number (no type ascription), so optimality of $u=0$ required $(p_j-\Delta V_{t+1}(x))u'\le0$ for every real $u'\le1$, which fails at $u'=-1$ exactly when rejecting is optimal (accepted disproof). The corrected module `Def_RevenueManagement_singleResource_v2` quantifies $u'$ over $\{0,1\}\subseteq\mathbb N$, which is the inner optimization of (2.17); every other declaration is unchanged. Conventions: $\lambda_j(t)\ge0$ with $\sum_j\lambda_j(t)\le1$ (at most one request per period), $V_{T+1}=0$ and $V_t(0)=0$, protection levels searched over $x=1,\dots,C$ with value $0$ for an empty set, and $y_0^*(t)=0$ since $\Delta V_{t+1}\le p_1$.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 59–61, Theorem 2.2 with Eq. (2.17)–(2.20) and the acceptance rule p_j ≥ ΔV_{t+1}(x) of Sect. 2.5.2

import Definitions.Def_RevenueManagement_singleResource_v2

namespace RevenueManagement

/-- Talluri & van Ryzin, *The Theory and Practice of Revenue Management*, pp. 59–61,
Theorem 2.2 with (2.18)–(2.20): in the dynamic model (2.17) with an arrival model, prices
`p_1 ≥ ⋯ ≥ p_n ≥ 0`, capacity `C` and period `1 ≤ t ≤ T`, the time-dependent protection levels
are nested, and for a class-`j` request with `1 ≤ x ≤ C` units remaining each of the controls
(i) accept iff `x > y*_{j−1}(t)` (protection levels), (ii) accept iff `C − x < b*_j(t)`
(booking limits), (iii) accept iff `p_j ≥ π_{t+1}(x)` (bid prices) maximizes
`(p_j − ΔV_{t+1}(x)) u` over `u ∈ {0, 1}`.

Corrected version: the statement is unchanged, but it imports the corrected definition module
in which `IsDynOptimal` compares `u` with the decisions `u' ∈ {0, 1}` only; in the retired
module the competitor `u'` was elaborated as a real number, so rejecting (`u = 0`) was never
"optimal" when `p_j < ΔV_{t+1}(x)`. -/
theorem dynamic_optimal_controls_v2 (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) :
    (∀ j, dynProtLevel lam p n T C t j ≤ dynProtLevel lam p n T C t (j + 1)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynProtLevel lam p n T C t (j - 1) < x then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if C - x < dynBookLimit lam p n T C t j then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynBidPrice lam p n T (t + 1) x ≤ p j then 1 else 0)) := by sorry

end RevenueManagement
