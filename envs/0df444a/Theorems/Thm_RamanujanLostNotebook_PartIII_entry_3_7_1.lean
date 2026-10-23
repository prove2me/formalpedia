-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartIII_entry_3_7_1
-- name    : RamanujanLostNotebook.PartIII.entry_3_7_1
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-11T09:05:41.161194+00:00
-- url     : https://prove2.me/theorems/2629d8aa-bdd6-413f-a2d8-dcfbc912bd14
-- title:
--   Eleven-dissection modulo S₅
-- statement:
--   Work in Z[a,a^(-1)][[q]]. Put F_a=(q;q)_infinity/((aq;q)_infinity(q/a;q)_infinity), A_m=a^m+a^(-m), S_m=sum_{k=-m}^m a^k, theta(r,s)=f(-q^r,-q^s), euler(d)=(q^d;q^d)_infinity, plus(d)=(-q^d;q^d)_infinity, L(m)=A_m and inv(P) the unique formal reciprocal of a series with constant term one. A=f(-q^55,-q^66); B=f(-q^77,-q^44); C=f(-q^88,-q^33); D=f(-q^99,-q^22); E=f(-q^110,-q^11). For every N>=0, the coefficient of q^N in F_a minus ((1)*(A*B*C*D) + (L(1)-1)*(q*A^2*B*E) + (L(2))*(q^2*A*C^2*D) + (L(3)+1)*(q^3*A*B*D^2) + (L(2)+L(4)+1)*(q^4*A*B*C*E) + (-L(2)-L(4))*(q^5*B^2*C*E) + (L(1)+L(4))*(q^7*A*B*D*E) + (-L(2)-L(5)-1)*(q^19*C*D*E^2) + (-L(4)-1)*(q^9*A*C*D*E) + (-L(3))*(q^10*B*C*D*E))*inv(euler(11))*inv(euler(121))^2 is divisible by S_5 in the integer Laurent polynomial ring. Differs from the printed source: the formal q-series congruence is encoded as divisibility of its exact degree-N integer Laurent coefficient for every N, using finite polynomial representatives and geometric reciprocals with constant term one. This is our representation choice, with no fixed cutoff or numerical hypothesis and no specialization of a to a root of unity. The independent pre-compile audit confirms this reading and recommends the current statement. At q=0.17, 0.63, 0.31+0.47i it reports absolute residuals 1.63e-70; 1.11e-70; 3.84e-71 for the printed expression and 1.63e-70; 2.18e-70; 1.18e-70 for the stated expression, with at least 65 scaled agreeing digits at 70-digit working precision; numerical evidence, not a proof. The audit also reports zero exact Laurent remainders in every degree 0–35; the theorem still quantifies over every N.
--
--   **Discrepancy from the printed source.** Differs from the printed source: the formal q-series congruence is encoded as divisibility of its exact degree-N integer Laurent coefficient for every N, using finite polynomial representatives and geometric reciprocals with constant term one. This is our representation choice, with no fixed cutoff or numerical hypothesis and no specialization of a to a root of unity. The independent pre-compile audit confirms this reading and recommends the current statement. At q=0.17, 0.63, 0.31+0.47i it reports absolute residuals 1.63e-70; 1.11e-70; 3.84e-71 for the printed expression and 1.63e-70; 2.18e-70; 1.18e-70 for the stated expression, with at least 65 scaled agreeing digits at 70-digit working precision; numerical evidence, not a proof. The audit also reports zero exact Laurent remainders in every degree 0–35; the theorem still quantifies over every N.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3, Entry 3.7.1, p. 63, unnumbered display.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3CrankTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3EulerTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3LaurentA
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3LaurentS
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3MonomialA
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3ThetaTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3UnitInvTrunc

namespace RamanujanLostNotebook.PartIII
theorem entry_3_7_1 (N : ℕ) :
    let Q : Polynomial (AddMonoidAlgebra ℤ ℤ) := Polynomial.X
    let A : Polynomial (AddMonoidAlgebra ℤ ℤ) := (ch3ThetaTrunc N 55 66)
    let B : Polynomial (AddMonoidAlgebra ℤ ℤ) := (ch3ThetaTrunc N 77 44)
    let C : Polynomial (AddMonoidAlgebra ℤ ℤ) := (ch3ThetaTrunc N 88 33)
    let D : Polynomial (AddMonoidAlgebra ℤ ℤ) := (ch3ThetaTrunc N 99 22)
    let E : Polynomial (AddMonoidAlgebra ℤ ℤ) := (ch3ThetaTrunc N 110 11)
    (ch3LaurentS 5) ∣
      (ch3CrankTrunc N - ((((((((((((1 * (((A * B) * C) * D)) + (((Polynomial.C (ch3LaurentA 1)) - 1) * (((Q * (A ^ 2)) * B) * E))) + ((Polynomial.C (ch3LaurentA 2)) * ((((Q ^ 2) * A) * (C ^ 2)) * D))) + (((Polynomial.C (ch3LaurentA 3)) + 1) * ((((Q ^ 3) * A) * B) * (D ^ 2)))) + ((((Polynomial.C (ch3LaurentA 2)) + (Polynomial.C (ch3LaurentA 4))) + 1) * (((((Q ^ 4) * A) * B) * C) * E))) + (((-((Polynomial.C (ch3LaurentA 2)))) - (Polynomial.C (ch3LaurentA 4))) * ((((Q ^ 5) * (B ^ 2)) * C) * E))) + (((Polynomial.C (ch3LaurentA 1)) + (Polynomial.C (ch3LaurentA 4))) * (((((Q ^ 7) * A) * B) * D) * E))) + ((((-((Polynomial.C (ch3LaurentA 2)))) - (Polynomial.C (ch3LaurentA 5))) - 1) * ((((Q ^ 19) * C) * D) * (E ^ 2)))) + (((-((Polynomial.C (ch3LaurentA 4)))) - 1) * (((((Q ^ 9) * A) * C) * D) * E))) + ((-((Polynomial.C (ch3LaurentA 3)))) * (((((Q ^ 10) * B) * C) * D) * E))) * (ch3UnitInvTrunc N (ch3EulerTrunc N 11))) * ((ch3UnitInvTrunc N (ch3EulerTrunc N 121)) ^ 2))).coeff N := by sorry
end RamanujanLostNotebook.PartIII
