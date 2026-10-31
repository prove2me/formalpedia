-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_coloredCycle_product
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.coloredCycle_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:15:24.151589+00:00
-- url     : https://prove2.me/theorems/042f4dad-377f-4859-b2ca-d81a632d2d0f
-- title:
--   All three products of colored cycles
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, and $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$. In $T\rtimes RS_d$ use $(pw)(qv)=p(w\cdot q)wv$ with $w\cdot x_i=x_{w(i)}$. A cycle $A$ carries its nonempty letter set, including the letter of a marked singleton. Put $A^{(r)}=h_r(A)A$, with $h_r$ the truncated symmetric sum of total degree $(|A|-1)(l-1)+r$. Let $A,B$ be cycles, $r,s\ge0$, and $c=|A\cap B|$.
--
--   1. If $c=0$, then $A^{(r)}B^{(s)}=B^{(s)}A^{(r)}$.
--   2. If $c=1$, the product $AB$ is a single cycle on $A\cup B$ and $A^{(r)}B^{(s)}=(AB)^{(r+s)}$.
--   3. If $c\ge2$, then
--
--   $$A^{(r)}B^{(s)}=\delta_{r+s,0}\,l^{c-1}h_{(c-1)(l-1)}(A\cup B)AB.$$
--
--   The delta equals one exactly when $r+s=0$. Colors at least $l$ give zero. These identities govern the algebra of colored cycles.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 5, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Lemma 2.2, PDF pp.5--6, all three cases. Only the c=1 branch asserts
that AB is a single cycle. The last coefficient includes the Kronecker delta. -/
theorem coloredCycle_product (R : Type*) [CommRing R] (l d : ℕ) (hl : 0 < l)
    (A B : MarkedCycle d) (r s : ℕ) :
    (((A.val.1 ∩ B.val.1).card = 0) →
      coloredCycle R l d A r * coloredCycle R l d B s =
        coloredCycle R l d B s * coloredCycle R l d A r) ∧
    (((A.val.1 ∩ B.val.1).card = 1) →
      IsMarkedCycle (A.val.1 ∪ B.val.1, A.val.2 * B.val.2) ∧
      coloredCycle R l d A r * coloredCycle R l d B s =
        hElement R l d (A.val.1 ∪ B.val.1) (r + s) *
          gradedW R l d (A.val.2 * B.val.2)) ∧
    ((2 ≤ (A.val.1 ∩ B.val.1).card) →
      coloredCycle R l d A r * coloredCycle R l d B s =
        (if r + s = 0 then (l : R) ^ ((A.val.1 ∩ B.val.1).card - 1) else 0) •
          (hElement R l d (A.val.1 ∪ B.val.1)
            (((A.val.1 ∩ B.val.1).card - 1) * (l - 1)) *
              gradedW R l d (A.val.2 * B.val.2))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
