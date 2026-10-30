-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_equation_10_1_1
-- name    : RamanujanLostNotebook.PartI.equation_10_1_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T02:38:57.840881+00:00
-- url     : https://prove2.me/theorems/2c2b3e86-baf4-41c4-96a5-1231a801bf1e
-- title:
--   Rogers–Ramanujan product identity 1
-- statement:
--   For every complex q with |q|<1, the series sum_(n≥0) q^(n²)/(q;q)_n has sum 1/((q^1;q^5)_infinity (q^4;q^5)_infinity); all finite denominators and both infinite denominator products are nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 10, Section 10.1, p. 241, eq. (10.1.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf
open scoped BigOperators

namespace RamanujanLostNotebook.PartI
theorem equation_10_1_1 (q : ℂ) (hq : ‖q‖ < 1) :
    (∀ n : ℕ, qPoch q q n ≠ 0) ∧
    qPochInf (q ^ 1) (q ^ 5) ≠ 0 ∧
    qPochInf (q ^ 4) (q ^ 5) ≠ 0 ∧
    HasSum (fun n : ℕ => q ^ (n ^ 2) / qPoch q q n)
      (1 / (qPochInf (q ^ 1) (q ^ 5) *
        qPochInf (q ^ 4) (q ^ 5))) := by sorry
end RamanujanLostNotebook.PartI
