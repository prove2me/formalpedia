-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_entry_4_2_1
-- name    : RamanujanLostNotebook.PartIII.entry_4_2_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T07:55:48.102301+00:00
-- url     : https://prove2.me/theorems/a14f38c3-69b2-44e9-acb8-10ad1fb4f7d3
-- title:
--   Double-series expansion of the squared Euler quotient
-- statement:
--   For complex a,q with |q|<min(|a|,1/|a|), the absolutely convergent sum over m>=1,n>=0 of (-1)^m q^{m(m+1)/2+mn}(a^{n+1}+a^{-n-1}-a^n-a^{-n}) equals one minus (q;q)_infty^2/((aq;q)_infty(q/a;q)_infty).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 4, Entry 4.2.1, p. 72, eq. (4.2.4).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch04_ch04DiffTerm
import Definitions.Def_RamanujanLostNotebook_PartIII_ch04_ch04Sym
import Definitions.Def_RamanujanLostNotebook_PartIII_shared_qPochInf

namespace RamanujanLostNotebook.PartIII
theorem entry_4_2_1 (a q : ℂ) (hq_a : ‖q‖ < ‖a‖) (hq_inv : ‖q‖ < 1 / ‖a‖) :
    HasSum (ch04DiffTerm a q) (1 - qPochInf q q ^ 2 / (qPochInf (a * q) q * qPochInf (q / a) q)) := by sorry
end RamanujanLostNotebook.PartIII
