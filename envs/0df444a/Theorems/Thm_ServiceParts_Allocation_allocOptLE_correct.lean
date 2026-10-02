-- Prove2me | Theorems.Thm_ServiceParts_Allocation_allocOptLE_correct
-- name    : ServiceParts.Allocation.allocOptLE_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T23:07:17.820252+00:00
-- url     : https://prove2.me/theorems/835e6a55-c94f-42cd-958e-fd1a7e0aa5bf
-- title:
--   Remark 2 — AllocOpt with the modified inner loop solves (7.22) under Σ r_m ≤ r⁰_n
-- statement:
--   Under the assumptions of Proposition 2 (see `allocOpt_correct`), modify step 7b of Algorithm AllocOpt to read "While $u > 0$ and $\hat c^{m^*}_{n^*(m^*)} \le 0$, do …". Then, for any tie-breaking rule in the $\arg\min$ steps, the values $c^0_n$ it returns satisfy, for every $n \in N_0$,
--   $$c^0_n = f(r^0_n) + \min_{\substack{r_m \ge 0,\ r_m \text{ integer},\ \forall m \in M;\\ \sum_{m \in M} r_m \le r^0_n}} \ \sum_{m \in M} \tilde C_m(r_m).$$
--
--   This is the form needed in (7.15) and (7.17), where stock not allocated to the lower echelon is retained at the higher one.
--
--   **Formalization Note** The minimum is stated as attainment by a feasible integer allocation plus a lower bound over all feasible integer allocations. The book calls the extension "trivial" and gives no proof.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 179, Remark 2

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData
import Definitions.Def_ServiceParts_Allocation_AllocOpt

namespace ServiceParts.Allocation

/-- Muckstadt (2005), Remark 2, p. 179: with the inner loop modified to "While `u > 0` and
`ĉ^{m*}_{n*(m*)} ≤ 0`", algorithm AllocOpt solves (7.22) with the constraint
`Σ_{m ∈ M} r_m ≤ r^0_k` in place of `Σ_{m ∈ M} r_m = r^0_k`. -/
theorem allocOptLE_correct {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (sel : (Fin Mbar → ℝ) → Fin Mbar) (hsel : IsArgminRule sel)
    (k : ℕ) (hk : k ≤ d.n0) :
    (∃ r : Fin Mbar → ℕ, ∑ m, (r m : ℤ) ≤ d.grid0 k ∧
        d.allocOptLE sel k = d.f (d.grid0 k) + ∑ m, d.pwl m (r m)) ∧
      ∀ r : Fin Mbar → ℕ, ∑ m, (r m : ℤ) ≤ d.grid0 k →
        d.allocOptLE sel k ≤ d.f (d.grid0 k) + ∑ m, d.pwl m (r m) := by sorry

end ServiceParts.Allocation
