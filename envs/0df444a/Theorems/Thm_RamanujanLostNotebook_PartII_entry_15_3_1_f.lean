-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_15_3_1_f
-- name    : RamanujanLostNotebook.PartII.entry_15_3_1_f
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T07:36:37.283116+00:00
-- url     : https://prove2.me/theorems/5a458be8-7ad4-4ac6-ad11-cf12fa89b4af
-- title:
--   Exact π equality at n=163
-- statement:
--   Define P(q)=1−24∑_{r≥1}rq^r/(1−q^r), Q(q)=1+240∑_{r≥1}r³q^r/(1−q^r), R(q)=1−504∑_{r≥1}r⁵q^r/(1−q^r), and P_n=P(−exp(−π√n)), Q_n=Q(−exp(−π√n)), R_n=R(−exp(−π√n)). At n=163, the Lambert series converge absolutely, Q_n>0, and (√n P_n−6/π)/√Q_n=362 * Real.sqrt (3 / 3335 : ℝ), with all roots positive real roots.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 15, Entry 15.3.1, p. 369.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertConverges
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15LambertTerm
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15Nome
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15P
import Definitions.Def_RamanujanLostNotebook_PartII_ch15_ch15Q

namespace RamanujanLostNotebook.PartII
theorem entry_15_3_1_f :
    ch15LambertConverges ((-ch15Nome (163 : ℝ) : ℝ) : ℂ) ∧ 0 < ch15Q (-ch15Nome (163 : ℝ)) ∧
      (Real.sqrt (163 : ℝ) * ch15P (-ch15Nome (163 : ℝ)) - 6 / Real.pi) / Real.sqrt (ch15Q (-ch15Nome (163 : ℝ))) =
        362 * Real.sqrt (3 / 3335 : ℝ) := by sorry
end RamanujanLostNotebook.PartII
