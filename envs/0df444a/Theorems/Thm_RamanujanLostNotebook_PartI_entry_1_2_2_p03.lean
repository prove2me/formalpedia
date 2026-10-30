-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartI_entry_1_2_2_p03
-- name    : RamanujanLostNotebook.PartI.entry_1_2_2_p03
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:23:57.711982+00:00
-- url     : https://prove2.me/theorems/136e6272-2a0c-4c54-ae72-6418af1c9c1d
-- title:
--   Reconstructed P,Q identity 3
-- statement:
--   Notation: ** means exponentiation; l denotes lambda. f(a,b)=sum over n in Z of a^(n(n+1)/2)*b^(n(n-1)/2); phi(z)=sum over n in Z of z^(n²); psi(z)=sum over n≥0 of z^(n(n+1)/2); e(z)=product over n≥1 of (1-z^n); chi(z)=product over n≥0 of (1+z^(2n+1)); poch(a,z)=product over n≥0 of (1-a*z^n). R(q)=q^(1/5)*poch(q,q⁵)*poch(q⁴,q⁵)/(poch(q²,q⁵)*poch(q³,q⁵)); rr(t) means R(exp(t)) with root exp(t/5). r=exp(t/5). D=f(-lambda¹⁰*q⁵,-lambda¹⁵*q¹⁰). P=(f(-lambda^10*q^7,-lambda^15*q^8)+lambda*q*f(-lambda^5*q^2,-lambda^20*q^13))/(r*D). Q=(lambda*f(-lambda^5*q^4,-lambda^20*q^11)-lambda^3*q*f(-q,-lambda^25*q^14))/(exp(-t/5)*D). For every complex t, set nonzero q=exp(t) and use q^a=exp(a*t), for every complex lambda with |lambda^5*q^3|<1, define P,Q by (1.2.9)–(1.2.10). Reconstructed P,Q identity 3. With the definitions below, P**5-Q**5 = 1+5*P*Q+5*P**2*Q**2+f(-q,-(l**5)*q**2)*f(-(l**2)*q,-(l**3)*q**2)**5/(q*D**6). Require these displayed denominators nonzero: D. Differs from the printed source: the notebook left P,Q unspecified; we use the book’s authors’ reconstructions (1.2.9)–(1.2.10). Differs from the printed source: we write nonzero q as exp(t), use q^a=exp(a*t), and explicitly require |lambda^5*q^3|<1 so all theta series converge. No restriction Re(t)<0 is imposed for this two-variable family. These analytic and branch conditions are our explicit interpretation. Differs from the printed source: we require nonzero displayed denominators (D); these regular-locus conditions are our explicit safeguards against totalized division. The independent pre-compile audit confirms the print and typed form agree on their common domain: printed maximum scaled residual 8.82e-81 (80 agreeing decimal digits), typed maximum scaled residual 8.82e-81 (80 agreeing decimal digits).
--
--   **Discrepancy from the printed source.** Differs from the printed source: the notebook left P,Q unspecified; we use the book’s authors’ reconstructions (1.2.9)–(1.2.10). Differs from the printed source: we write nonzero q as exp(t), use q^a=exp(a*t), and explicitly require |lambda^5*q^3|<1 so all theta series converge. No restriction Re(t)<0 is imposed for this two-variable family. These analytic and branch conditions are our explicit interpretation. Differs from the printed source: we require nonzero displayed denominators (D); these regular-locus conditions are our explicit safeguards against totalized division. The independent pre-compile audit confirms the print and typed form agree on their common domain: printed maximum scaled residual 8.82e-81 (80 agreeing decimal digits), typed maximum scaled residual 8.82e-81 (80 agreeing decimal digits).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 1, Entry 1.2.2, p. 13, eq. (1.2.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch01_ch1P
import Definitions.Def_RamanujanLostNotebook_PartI_ch01_ch1Q
import Definitions.Def_RamanujanLostNotebook_PartI_shared_ramanujanTheta

namespace RamanujanLostNotebook.PartI
theorem entry_1_2_2_p03 (t : ℂ) (l : ℂ) (hl : ‖l ^ 5 * Complex.exp (3 * t)‖ < 1) (hden1 : (ramanujanTheta (((-(l ^ 10)) * ((Complex.exp (t)) ^ 5))) (((-(l ^ 15)) * ((Complex.exp (t)) ^ 10)))) ≠ 0) :
    (((ch1P (l) (t)) ^ 5) - ((ch1Q (l) (t)) ^ 5)) = (((1 + ((5 * (ch1P (l) (t))) * (ch1Q (l) (t)))) + ((5 * ((ch1P (l) (t)) ^ 2)) * ((ch1Q (l) (t)) ^ 2))) + (((ramanujanTheta ((-(Complex.exp (t)))) (((-(l ^ 5)) * ((Complex.exp (t)) ^ 2)))) * ((ramanujanTheta (((-(l ^ 2)) * (Complex.exp (t)))) (((-(l ^ 3)) * ((Complex.exp (t)) ^ 2)))) ^ 5)) / ((Complex.exp (t)) * ((ramanujanTheta (((-(l ^ 10)) * ((Complex.exp (t)) ^ 5))) (((-(l ^ 15)) * ((Complex.exp (t)) ^ 10)))) ^ 6)))) := by sorry
end RamanujanLostNotebook.PartI
