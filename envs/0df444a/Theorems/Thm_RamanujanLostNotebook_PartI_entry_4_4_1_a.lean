-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_4_4_1_a
-- name    : RamanujanLostNotebook.PartI.entry_4_4_1_a
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T12:02:35.292536+00:00
-- url     : https://prove2.me/theorems/6925263f-849d-41b9-b1d7-76a12de64d3f
-- title:
--   Cubic reciprocal as a Lambert quotient
-- statement:
--   Define C(q)=∏_{k≥0}(1−q^{5k+2})(1−q^{5k+3})/((1−q^{5k+1})(1−q^{5k+4})); let v_n and u_n be the integer Taylor coefficients of C and 1/C respectively. Write L_{m,i,j}(q)=∑_{n∈ℤ}q^{in}/(1−q^{mn+j}), and K_j(q,n)=q^{5n²+2jn}(1+q^{5n+j})/(1−q^{5n+j}). For complex 0<|q|<1, 1/C(q)³=L_{5,2,2}(q)/L_{5,1,1}(q). All displayed series converge absolutely, and C(q) and the quotient denominator are nonzero. Differs from the printed source: The printed chapter disk includes q=0; we require q≠0 for the negative integer powers in the bilateral Lambert series. This domain restriction is ours; no value obtained by totalized division at zero is asserted. This revision independently recomputed the stated expression at 60 digits, including complex q=.3+.4i and q=.55,.65, with maximum residual 7.89698324742e-61; finite numerical evidence, not a proof.
--
--   **Discrepancy from the printed source.** The printed chapter disk includes q=0; we require q≠0 for the negative integer powers in the bilateral Lambert series. This domain restriction is ours; no value obtained by totalized division at zero is asserted. This revision independently recomputed the stated expression at 60 digits, including complex q=.3+.4i and q=.55,.65, with maximum residual 7.89698324742e-61; finite numerical evidence, not a proof.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 4, Entry 4.4.1, p. 117, eq. (4.4.1).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch04_ch04C
import Definitions.Def_RamanujanLostNotebook_PartI_ch04_ch04LambertTerm
import Definitions.Def_RamanujanLostNotebook_PartI_shared_qPochInf

namespace RamanujanLostNotebook.PartI
theorem entry_4_4_1_a (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    ch04C q ≠ 0 ∧ Summable (ch04LambertTerm 5 2 2 q) ∧ Summable (ch04LambertTerm 5 1 1 q) ∧
    (∑' n : ℤ, ch04LambertTerm 5 1 1 q n) ≠ 0 ∧ 1 / ch04C q ^ 3 = (∑' n : ℤ, ch04LambertTerm 5 2 2 q n) / (∑' n : ℤ, ch04LambertTerm 5 1 1 q n) := by sorry
end RamanujanLostNotebook.PartI
