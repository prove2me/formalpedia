-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartII_entry_6_3_3
-- name    : RamanujanLostNotebook.PartII.entry_6_3_3
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:26:19.536049+00:00
-- url     : https://prove2.me/theorems/a6d63646-6a69-43f5-90ce-1368ee4b58ae
-- title:
--   Ramanujan reciprocity
-- statement:
--   Write (x;r)_k=∏_{j=0}^{k−1}(1−x r^j), (x;r)_∞=∏_{j≥0}(1−x r^j). All parameters are complex and |q|<1. s sums n≥0, bt sums all integers, fs(f,M) sums 0≤n<M; qp and ip denote these finite and infinite symbols. th(x,y)=∑_{j∈ℤ}x^{j(j+1)/2}y^{j(j−1)/2}; psi(q)=∑_{n≥0}q^{n(n+1)/2}, phi(q)=∑_{j∈ℤ}q^{j²}, ef(q)=(q;q)_∞, pt(a,q)=∑_{n≥0}a^nq^{n(n+1)/2}, omega=exp(2πi/3). In the displayed executable notation, lambda n: E means n↦E, ** means exponentiation, and // means exact integer division; //2 is exact at all specified indices. The Lean names qPoch, qPochInf, ramanujanTheta, thetaPhi, thetaPsi, eulerF, ch06PartialTheta, and ch06WarnaarKernel correspond to qp, ip, th, phi, psi, ef, pt, and wk respectively. The following must be nonzero: a, b. Additional hypotheses, in explicit mathematical syntax: ∀ k : ℕ, qPoch ((-a) * q) q k ≠ 0; ∀ k : ℕ, qPoch ((-b) * q) q k ≠ 0; (qPochInf ((-a) * q) q) ≠ 0; (qPochInf ((-b) * q) q) ≠ 0. The identity is (1+1/b)*s(lambda n: (-1)**n*a**n*(1/b)**n*q**(n*(n+1)//2)/qp(-a*q,q,n))-(1+1/a)*s(lambda n: (-1)**n*(1/a)**n*b**n*q**(n*(n+1)//2)/qp(-b*q,q,n)) = (1/b-1/a)*ip(a*q/b,q)*ip(b*q/a,q)*ip(q,q)/(ip(-a*q,q)*ip(-b*q,q)). All infinite families in this expression are summable or multipliable, as asserted in the conclusion. Differs from the printed source: We explicitly restrict every finite/product/theta quotient to its nonzero-denominator locus; the print does not always list these conditions. The independent pre-compile audit confirms the regular-locus interpretation; maximum scaled residual ≤4.26e-70 (numerical evidence, not a proof).
--
--   **Discrepancy from the printed source.** We explicitly restrict every finite/product/theta quotient to its nonzero-denominator locus; the print does not always list these conditions. The independent pre-compile audit confirms the regular-locus interpretation; maximum scaled residual ≤4.26e-70 (numerical evidence, not a proof).
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 6, Entry 6.3.3, p. 116.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPoch
import Definitions.Def_RamanujanLostNotebook_PartII_shared_qPochInf

namespace RamanujanLostNotebook.PartII
theorem entry_6_3_3 (q a b : ℂ) (hq : ‖q‖ < 1) (h_a : a ≠ 0) (h_b : b ≠ 0)
    (hden1 : ∀ k : ℕ, qPoch ((-a) * q) q k ≠ 0)
    (hden2 : ∀ k : ℕ, qPoch ((-b) * q) q k ≠ 0)
    (hden3 : (qPochInf ((-a) * q) q) ≠ 0)
    (hden4 : (qPochInf ((-b) * q) q) ≠ 0) :
    (Summable (fun n : ℕ => ((((((-1) ^ n) * (a ^ n)) * ((1 / b) ^ n)) * (q ^ ((n * (n + 1)) / 2))) / (qPoch ((-a) * q) q n)))) ∧
    (Summable (fun n : ℕ => ((((((-1) ^ n) * ((1 / a) ^ n)) * (b ^ n)) * (q ^ ((n * (n + 1)) / 2))) / (qPoch ((-b) * q) q n)))) ∧
    (Multipliable (fun k : ℕ => 1 - ((a * q) / b) * q ^ k)) ∧
    (Multipliable (fun k : ℕ => 1 - ((b * q) / a) * q ^ k)) ∧
    (Multipliable (fun k : ℕ => 1 - q * q ^ k)) ∧
    (Multipliable (fun k : ℕ => 1 - ((-a) * q) * q ^ k)) ∧
    (Multipliable (fun k : ℕ => 1 - ((-b) * q) * q ^ k)) ∧
    ((((1 + (1 / b)) * (∑' n : ℕ, ((((((-1) ^ n) * (a ^ n)) * ((1 / b) ^ n)) * (q ^ ((n * (n + 1)) / 2))) / (qPoch ((-a) * q) q n)))) - ((1 + (1 / a)) * (∑' n : ℕ, ((((((-1) ^ n) * ((1 / a) ^ n)) * (b ^ n)) * (q ^ ((n * (n + 1)) / 2))) / (qPoch ((-b) * q) q n))))) = ((((((1 / b) - (1 / a)) * (qPochInf ((a * q) / b) q)) * (qPochInf ((b * q) / a) q)) * (qPochInf q q)) / ((qPochInf ((-a) * q) q) * (qPochInf ((-b) * q) q)))) := by sorry
end RamanujanLostNotebook.PartII
