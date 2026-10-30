-- Prove2me | Theorems.Thm_RamanujanLostNotebook_PartV_entry_15_2_1
-- name    : RamanujanLostNotebook.PartV.entry_15_2_1
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-10-06T18:35:08.337085+00:00
-- url     : https://prove2.me/theorems/b0cd2cb6-2c2b-4436-9433-a481436bcf5a
-- title:
--   Euler product for q f(-q)^3 f(-q^7)^3 with c_q = 7v^2 - u^2
-- statement:
--   Define integers $a_n$ by $\sum_{n\ge1}a_nq^n=q\,(q;q)_\infty^3(q^7;q^7)_\infty^3$ ($|q|<1$). For primes $\ell\equiv1,2,4\pmod 7$ put $c_2=\tfrac32$ and $c_\ell=7v^2-u^2$ if $\ell=u^2+7v^2$. Then for $\operatorname{Re}s>2$, $$\sum_{n\ge1}\frac{a_n}{n^s}=\frac{1}{1+7^{1-s}}\prod_{p\equiv3,5,6\ (7)}\frac{1}{1-p^{2(1-s)}}\prod_{\ell\equiv1,2,4\ (7)}\frac{1}{1+2c_\ell \ell^{-s}+\ell^{2(1-s)}},$$ both sides converging absolutely. Differs from the printed source: the book gives no half-plane; $\operatorname{Re}s>2$ (absolute convergence) is our restriction.
--
--   **Discrepancy from the printed source.** The book states no half-plane for this formula. Stated here for Re s > 2, the half-plane of absolute convergence of both sides (the coefficients satisfy |a(p)| <= 2 p^((k-1)/2) with k = 3 the weight of the underlying Hecke eigenform (elementary here, since a(p) is a sum of two conjugate algebraic integers of absolute value p^((k-1)/2); Deligne's theorem in general)); this restriction is ours, not a correction of the mathematics.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 15, Entry 15.2.1, p. 323, eq. (15.2.2), (15.2.3).

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartV_ch15_DirichletEulerEq
import Definitions.Def_RamanujanLostNotebook_PartV_ch15_IsCoeffSeq
import Definitions.Def_RamanujanLostNotebook_PartV_shared_eulerF
import Definitions.Def_RamanujanLostNotebook_PartV_shared_qPochInf

namespace RamanujanLostNotebook.PartV
theorem entry_15_2_1 (a : ℕ → ℤ)
    (ha : IsCoeffSeq a (fun q : ℂ => q * eulerF q ^ 3 * eulerF (q ^ 7) ^ 3))
    (c : ℕ → ℚ) (hc2 : c 2 = 3 / 2)
    (hc : ∀ p : ℕ, Nat.Prime p → ∀ u v : ℤ, (p : ℤ) = u ^ 2 + 7 * v ^ 2 →
      c p = ((7 * v ^ 2 - u ^ 2 : ℤ) : ℚ))
    (s : ℂ) (hs : 2 < s.re) :
    DirichletEulerEq (fun n : ℕ => ((a n : ℤ) : ℂ))
      (fun p : Nat.Primes =>
        (if (p : ℕ) = 7 then 1 / (1 + (7 : ℂ) ^ (1 - s)) else 1) *
        (if (p : ℕ) % 7 = 3 ∨ (p : ℕ) % 7 = 5 ∨ (p : ℕ) % 7 = 6 then
          1 / (1 - ((p : ℕ) : ℂ) ^ (2 * (1 - s))) else 1) *
        (if (p : ℕ) % 7 = 1 ∨ (p : ℕ) % 7 = 2 ∨ (p : ℕ) % 7 = 4 then
          1 / (1 + 2 * ((c (p : ℕ) : ℚ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (2 * (1 - s)))
          else 1)) s := by sorry
end RamanujanLostNotebook.PartV
