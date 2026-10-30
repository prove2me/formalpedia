-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_11_2_1_a
-- name    : RamanujanLostNotebook.PartI.entry_11_2_1_a
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T04:30:17.803173+00:00
-- url     : https://prove2.me/theorems/5e202a75-36f3-4890-b34f-6c6adccfc70c
-- title:
--   Rogers–Ramanujan–Slater series identity (11.2.1)
-- statement:
--   Write (a;b)_m=∏_{k=0}^{m-1}(1-ab^k) and (a;b)_∞=∏_{k≥0}(1-ab^k). G(u)=∑_{m≥0}u^{m²}/(u;u)_m, H(u)=∑_{m≥0}u^{m²+m}/(u;u)_m, phi(u)=∑_{k∈ℤ}u^{k²}, and f(a,b)=∑_{k∈ℤ}a^{k(k+1)/2}b^{k(k-1)/2}. For every complex q with |q|<1, ∑ q^{n²}/(q;q)_{2n}=G(q⁴)/(q;q²)_∞. All unilateral sums start at n=0, both sides converge absolutely, and all displayed denominators are nonzero. Differs from the printed source: we make the implicit analytic domain |q|<1 explicit, require absolute convergence in the conclusion via HasSum, and assert all displayed denominators are nonzero; these semantic conditions are our additions, with no change to the formula.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we make the implicit analytic domain |q|<1 explicit, require absolute convergence in the conclusion via HasSum, and assert all displayed denominators are nonzero; these semantic conditions are our additions, with no change to the formula.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 11, Entry 11.2.1, p. 252, eq. (11.2.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf
import Definitions.Def_RamanujanLostNotebook_PartI_shared_rrG

namespace RamanujanLostNotebook.PartI
theorem entry_11_2_1_a (q : ℂ) (hq : ‖q‖ < 1) :
    (∀ n : ℕ, qPoch q q (2 * n) ≠ 0) ∧
    qPochInf q (q ^ 2) ≠ 0 ∧
    HasSum (fun n : ℕ => q ^ (n ^ 2) / qPoch q q (2 * n))
      (rrG (q ^ 4) / qPochInf q (q ^ 2)) := by sorry
end RamanujanLostNotebook.PartI
