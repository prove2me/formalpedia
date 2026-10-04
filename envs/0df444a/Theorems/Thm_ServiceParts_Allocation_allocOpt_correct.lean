-- Prove2me | Theorems.Thm_ServiceParts_Allocation_allocOpt_correct
-- name    : ServiceParts.Allocation.allocOpt_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:04:57.131275+00:00
-- url     : https://prove2.me/theorems/1f01df81-9361-4d6a-8e60-2734aa95138d
-- title:
--   Proposition 2 — algorithm AllocOpt solves the allocation optimization (7.22)
-- statement:
--   Let the data of Section 7.4 satisfy its standing assumptions (see `AllocData`): locations $M = \{1, \dots, \bar M\}$ with $\bar M \ge 1$, integer gridpoints $0 = r^m_0 < \cdots < r^m_{n(m)}$ with $n(m) \ge 1$ for $m \in M$ and $0 = r^0_0 < \cdots < r^0_{n(0)}$ for location $0$, values $c^m_n$ of convex functions at the gridpoints, the slopes $\hat c^m_n$ of (7.19), the piecewise linear functions $\tilde C_m$ of (7.20)–(7.21), and a convex function $f$ on $\mathbb R_+$.
--
--   Then Algorithm AllocOpt (Definition 4), run with any rule for breaking ties in its $\arg\min$ steps, terminates with values $c^0 = (c^0_n)_{n \in N_0}$ that satisfy (7.22) for every $n \in N_0 = \{0, 1, \dots, n(0)\}$:
--   $$c^0_n = f(r^0_n) + \min_{\substack{r_m \ge 0,\ r_m \text{ integer},\ \forall m \in M;\\ \sum_{m \in M} r_m = r^0_n}} \ \sum_{m \in M} \tilde C_m(r_m).$$
--
--   In words, marginal allocation — repeatedly giving the next block of units to the location whose current marginal cost $\hat c^m_{n^*(m)}$ is smallest — solves the separable convex piecewise linear allocation problem exactly, simultaneously for every target total $r^0_n$. In Section 7.3 this computes the nested cost functions (7.14), (7.15) and (7.17) of the multi-echelon pooling model.
--
--   **Formalization Note** The book's Proposition 2 also bounds the number of calculations by $O\bigl((1 + \log_2 \bar M) \sum_{m \in M_0} n(m)\bigr)$; that half is not stated (an operation count with no machine model). The minimum is stated as (a) some feasible integer allocation $r = (r_m)$ attains the value and (b) no feasible integer allocation has a smaller value. Termination is structural in Lean (see `AllocOpt`). The tie-breaking rule is universally quantified; the book leaves it open.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 179, Proposition 2 (first sentence), with Eq. (7.22) on p. 178 and Definition 4 on pp. 178-179

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData
import Definitions.Def_ServiceParts_Allocation_AllocOpt

namespace ServiceParts.Allocation

/-- Muckstadt (2005), Proposition 2, p. 179 (correctness half): algorithm AllocOpt
(Definition 4) terminates with values `c^0_k` satisfying (7.22) for each `k ∈ N₀`:
`c^0_k = f(r^0_k) + min { Σ_{m ∈ M} Ĉ_m(r_m) : r_m ≥ 0 integer, Σ_{m ∈ M} r_m = r^0_k }`.
The minimum is stated as attainment plus lower bound. Termination is structural in Lean.
Stated for every tie-breaking rule of the arg min. -/
theorem allocOpt_correct {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (sel : (Fin Mbar → ℝ) → Fin Mbar) (hsel : IsArgminRule sel)
    (k : ℕ) (hk : k ≤ d.n0) :
    (∃ r : Fin Mbar → ℕ, ∑ m, (r m : ℤ) = d.grid0 k ∧
        d.allocOpt sel k = d.f (d.grid0 k) + ∑ m, d.pwl m (r m)) ∧
      ∀ r : Fin Mbar → ℕ, ∑ m, (r m : ℤ) = d.grid0 k →
        d.allocOpt sel k ≤ d.f (d.grid0 k) + ∑ m, d.pwl m (r m) := by sorry

end ServiceParts.Allocation
