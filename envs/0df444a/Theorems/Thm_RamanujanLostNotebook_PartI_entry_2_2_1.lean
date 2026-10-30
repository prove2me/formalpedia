-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_2_2_1
-- name    : RamanujanLostNotebook.PartI.entry_2_2_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:37:04.105208+00:00
-- url     : https://prove2.me/theorems/5d7cfb3a-7f09-40d7-9165-a571362b7583
-- title:
--   Explicit S evaluation
-- statement:
--   Define (a;q)_j=prod_{0<=k<j}(1-a*q^k); G(q)=sum_{j>=0}q^(j^2)/(q;q)_j; H(q)=sum_{j>=0}q^(j^2+j)/(q;q)_j; S(q;r)=r*H(-q)/G(-q) for the same r; S(q)=S(q;q^(1/5)), with the positive real fifth root. All sums and products are on the indicated convergent domains. Explicit S evaluation. Entry 2.2.1, printed p.59 / one-based PDF p.69.
--   Domain/quantifiers: a fixed-value identity, with no free parameters.
--   Assertion (with the definitions above): (rrG (((-Real.exp (((-Real.pi) * Real.sqrt (3)))) : ℂ))) ≠ 0 ∧ 0 ≤ ((6 * (5 + Real.sqrt (5)))) ∧ ch02SReal (Real.exp (((-Real.pi) * Real.sqrt (3)))) = (((-(3 + Real.sqrt (5))) + Real.sqrt ((6 * (5 + Real.sqrt (5))))) / 4) .
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 2, Entry 2.2.1, p. 59, eq. (2.2.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch02_ch02S
import Definitions.Def_RamanujanLostNotebook_PartI_ch02_ch02SReal
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartI_shared_rrG
import Definitions.Def_RamanujanLostNotebook_PartI_shared_rrH

namespace RamanujanLostNotebook.PartI
theorem entry_2_2_1  :
    (rrG (((-Real.exp (((-Real.pi) * Real.sqrt (3)))) : ℂ))) ≠ 0 ∧
    0 ≤ ((6 * (5 + Real.sqrt (5)))) ∧
    ch02SReal (Real.exp (((-Real.pi) * Real.sqrt (3)))) =
      (((-(3 + Real.sqrt (5))) + Real.sqrt ((6 * (5 + Real.sqrt (5))))) / 4) := by sorry
end RamanujanLostNotebook.PartI
