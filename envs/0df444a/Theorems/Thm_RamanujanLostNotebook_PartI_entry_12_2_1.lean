-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_12_2_1
-- name    : RamanujanLostNotebook.PartI.entry_12_2_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T04:31:36.229219+00:00
-- url     : https://prove2.me/theorems/036ef3c0-b93c-4f1c-9b9c-0dd435d9fd66
-- title:
--   Bilateral partial fractions for a quadratic q-series
-- statement:
--   Let q be complex with 0<|q|<1, and let a be a nonzero complex number. Conventions: qPoch(x,b,n)=∏_{k=0}^{n−1}(1−x b^k); qPochInf(x,b)=∏_{k≥0}(1−x b^k). Assume ∀ n : ℤ, (1 + (a * (q ^ (2 * n)))) ≠ 0; ∀ n : ℕ, ((qPoch ((-a)) ((q ^ 2)) ((n + 1))) * (qPoch (((-(q ^ 2)) / a)) ((q ^ 2)) (n))) ≠ 0; (qPochInf ((q ^ 2)) ((q ^ 2))) ≠ 0. Put s0(n)=((q ^ ((2 * (n ^ 2)) + n)) / (1 + (a * (q ^ (2 * n))))) (n∈ℤ); s1(n)=(((((-1) ^ n) * (qPoch (q) ((q ^ 2)) (n))) * (q ^ (n ^ 2))) / ((qPoch ((-a)) ((q ^ 2)) ((n + 1))) * (qPoch (((-(q ^ 2)) / a)) ((q ^ 2)) (n)))) (n∈ℕ). Then every listed series is absolutely convergent and, writing Sj=∑s_j(n) over its stated index set, (((qPochInf (q) ((q ^ 2))) / (qPochInf ((q ^ 2)) ((q ^ 2)))) * S0) = S1. Differs from the printed source: we make the implicit open-disk domain and all denominator nonvanishing conditions explicit, and assert convergence in the conclusion rather than assume it. We use 0<|q|<1 because integer powers in bilateral denominators require q≠0; the possible removable q=0 limit is not asserted.
--
--   **Discrepancy from the printed source.** Differs from the printed source: we make the implicit open-disk domain and all denominator nonvanishing conditions explicit, and assert convergence in the conclusion rather than assume it. We use 0<|q|<1 because integer powers in bilateral denominators require q≠0; the possible removable q=0 limit is not asserted.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 12, Entry 12.2.1, p. 264, eq. (12.2.6).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf

namespace RamanujanLostNotebook.PartI
theorem entry_12_2_1 (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (a : ℂ) (ha : a ≠ 0)
    (hd0 : ∀ n : ℤ, (1 + (a * (q ^ (2 * n)))) ≠ 0)
    (hd1 : ∀ n : ℕ, ((qPoch ((-a)) ((q ^ 2)) ((n + 1))) * (qPoch (((-(q ^ 2)) / a)) ((q ^ 2)) (n))) ≠ 0)
    (hd2 : (qPochInf ((q ^ 2)) ((q ^ 2))) ≠ 0) :
    let s0 : ℤ → ℂ := fun n => ((q ^ ((2 * (n ^ 2)) + n)) / (1 + (a * (q ^ (2 * n)))))
    let s1 : ℕ → ℂ := fun n => (((((-1 : ℂ) ^ n) * (qPoch (q) ((q ^ 2)) (n))) * (q ^ (n ^ 2))) / ((qPoch ((-a)) ((q ^ 2)) ((n + 1))) * (qPoch (((-(q ^ 2)) / a)) ((q ^ 2)) (n))))
    Summable s0 ∧ Summable s1 ∧
      (((qPochInf (q) ((q ^ 2))) / (qPochInf ((q ^ 2)) ((q ^ 2)))) * (∑' n : ℤ, s0 n)) = (∑' n : ℕ, s1 n) := by sorry
end RamanujanLostNotebook.PartI
