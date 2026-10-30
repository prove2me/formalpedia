-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_entry_6_2_1
-- name    : RamanujanLostNotebook.PartIII.entry_6_2_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T06:38:32.418806+00:00
-- url     : https://prove2.me/theorems/8f05a092-e9b9-412b-8fed-2a2776d4fedf
-- title:
--   Partition dissection for modulus five
-- statement:
--   For every complex q with |q|<1, the series ∑_{n≥0}p(5n+4)q^n converges absolutely to 5(q^5;q^5)_∞^5/(q;q)_∞^6, where p(n) is the coefficient of (q;q)_∞^(-1). The denominator is nonzero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 6, Entry 6.2.1, p. 183, eq. (6.2.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch06_ch6EulerPower
import Definitions.Def_RamanujanLostNotebook_PartIII_ch06_ch6Pr
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_eulerF
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf

namespace RamanujanLostNotebook.PartIII
theorem entry_6_2_1 (q : ℂ) (hq : ‖q‖ < 1) :
    eulerF q ≠ 0 ∧
      HasSum (fun n : ℕ => (ch6Pr 1 ((5 * n + 4 : ℕ) : ℤ) : ℂ) * q ^ n)
        (5 * eulerF (q ^ 5) ^ 5 / eulerF q ^ 6) := by sorry
end RamanujanLostNotebook.PartIII
