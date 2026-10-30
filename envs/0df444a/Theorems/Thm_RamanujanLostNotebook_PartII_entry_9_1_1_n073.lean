-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_9_1_1_n073
-- name    : RamanujanLostNotebook.PartII.entry_9_1_1_n073
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T11:21:30.745341+00:00
-- url     : https://prove2.me/theorems/755c6b3a-41e4-4892-bd93-0d18ac87aae3
-- title:
--   Cubic invariant at index 73
-- statement:
--   For x>0, qₓ=exp(−π√(x/3)), f(z)=∏_{k≥1}(1−(−z)^k), and λₓ=qₓ^(−1/2)(f(qₓ)/f(qₓ³))⁶/(3√3). λ 73 = (sqrt ((11 + sqrt 73) / 8) + sqrt ((3 + sqrt 73) / 8)) ^ 6. Products appearing in this formula converge to nonzero values and the real invariants are positive; when J is used, its lattice sums converge, its discriminant is nonzero and j is real. Differs from the printed source: the ellipsis in (9.1.1), p.195, is replaced by the completely specified quotient f(q)/f(q³) of (9.1.4), p.196. Thus its factors are 1−(−q)^k for k≥1 with 3∤k. This is our explicit interpretation of the ellipsis, supported by the book’s own alternative definition; no listed radical is changed. Extending the ellipsis as (1+q)∏(1−q^(2k)) instead gives 0.99917822861114612895 at n=1, rather than 1 (numerical evidence, not a proof).
--   Differs from the printed source: convergence, nonvanishing and positivity implicit in the analytic invariants are explicit conclusions here; they are not added hypotheses.
--   An independent pre-compile audit confirms this disclosed formula choice: its printed/competing scaled residual (agreeing digits) is 1.33846698466e-33 (32.873392), and its stated-formula residual (agreeing digits) is 2.77765781501e-120 (119.55632). These are the auditor's numerical results, not a proof or a compilation result.
--
--   **Discrepancy from the printed source.** Differs from the printed source: the ellipsis in (9.1.1), p.195, is replaced by the completely specified quotient f(q)/f(q³) of (9.1.4), p.196. Thus its factors are 1−(−q)^k for k≥1 with 3∤k. This is our explicit interpretation of the ellipsis, supported by the book’s own alternative definition; no listed radical is changed. Extending the ellipsis as (1+q)∏(1−q^(2k)) instead gives 0.99917822861114612895 at n=1, rather than 1 (numerical evidence, not a proof).
--   Differs from the printed source: convergence, nonvanishing and positivity implicit in the analytic invariants are explicit conclusions here; they are not added hypotheses.
--   An independent pre-compile audit confirms this disclosed formula choice: its printed/competing scaled residual (agreeing digits) is 1.33846698466e-33 (32.873392), and its stated-formula residual (agreeing digits) is 2.77765781501e-120 (119.55632). These are the auditor's numerical results, not a proof or a compilation result.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 9, Entry 9.1.1, p. 195.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09EulerRegular
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09F
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Lambda
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09LambdaRegular
import Definitions.Def_RamanujanLostNotebook_PartII_ch09_ch09Nome
import Definitions.Def_RamanujanLostNotebook_PartII_shared_eulerF
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem entry_9_1_1_n073  :
    ch09LambdaRegular 73 ∧
    (ch09Lambda 73 =
      (Real.sqrt ((11 + Real.sqrt 73) / 8) + Real.sqrt ((3 + Real.sqrt 73) / 8)) ^ 6) := by sorry
end RamanujanLostNotebook.PartII
