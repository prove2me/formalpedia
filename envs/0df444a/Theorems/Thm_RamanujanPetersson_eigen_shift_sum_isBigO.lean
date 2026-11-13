-- Prove2me | Theorems.Thm_RamanujanPetersson_eigen_shift_sum_isBigO
-- name    : RamanujanPetersson.eigen_shift_sum_isBigO
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T01:30:18.619597+00:00
-- url     : https://prove2.me/theorems/1013458f-ffe4-4881-8212-048b73812b2d
-- title:
--   Elementary assembly: a finite combination of shifted Hecke-multiplicative sequences with root bounds is $O(n^{(k-1)/2+\varepsilon})$
-- statement:
--   Let $k\ge1$, $\varepsilon>0$, and for $i$ in a finite index set let $c_i\in\mathbb C$, $d_i\ge1$, $L_i\in\mathbb N$, $\chi_i$ a Dirichlet character mod $L_i$ and $b_i:\mathbb N\to\mathbb C$ with $b_i(1)=1$, with, for every prime $p$ and $n\ge0$,
--
--   $$b_i(pn)=b_i(p)b_i(n)-\mathbf 1_{p\nmid L_i}\,\chi_i(p)p^{k-1}\,b_i(n/p)\quad(b_i(n/p)=0\text{ if }p\nmid n),$$
--
--   with $|b_i(p)|\le p^{(k-1)/2}$ for primes $p\mid L_i$, and such that for primes $p\nmid L_i$ every root of $X^2-b_i(p)X+\chi_i(p)p^{k-1}$ has absolute value at most $p^{(k-1)/2}$. Then
--
--   $$\sum_i c_i\, b_i(n/d_i)=O\big(n^{(k-1)/2+\varepsilon}\big)\qquad(n\to\infty),$$
--
--   where $b_i(n/d_i)=0$ when $d_i\nmid n$.
--
--   Role: the elementary part of Ramanujan–Petersson: multiplicativity, $|b(p^r)|\le(r+1)p^{r(k-1)/2}$, the divisor bound $d(n)=O(n^{\varepsilon})$ and the finite sum.
-- source:
--   G. H. Hardy, E. M. Wright, An Introduction to the Theory of Numbers, Theorem 315 ($d(n)=O(n^\varepsilon)$); F. Diamond, J. Shurman, A First Course in Modular Forms (GTM 228), Springer 2005, https://doi.org/10.1007/978-0-387-27226-9, Proposition 5.8.5 (Hecke recursion of normalized eigenform coefficients)

import Mathlib
open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

namespace RamanujanPetersson

theorem eigen_shift_sum_isBigO (k : ℤ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (r : ℕ)
    (c : Fin r → ℂ) (d L : Fin r → ℕ) (χ : (i : Fin r) → DirichletCharacter ℂ (L i))
    (b : Fin r → ℕ → ℂ) (hd : ∀ i, 0 < d i) (h1 : ∀ i, b i 1 = 1)
    (hrec : ∀ i, ∀ p n : ℕ, p.Prime →
      b i (p * n) = b i p * b i n -
        (if p ∣ L i then 0 else
          χ i (p : ZMod (L i)) * (p : ℂ) ^ (k - 1) * (if p ∣ n then b i (n / p) else 0)))
    (hbad : ∀ i, ∀ p : ℕ, p.Prime → p ∣ L i → ‖b i p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2))
    (hroot : ∀ i, ∀ p : ℕ, p.Prime → ¬ p ∣ L i → ∀ α : ℂ,
      α ^ 2 - b i p * α + χ i (p : ZMod (L i)) * (p : ℂ) ^ (k - 1) = 0 →
        ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    (fun n : ℕ => ∑ i, c i * (if d i ∣ n then b i (n / d i) else 0))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by sorry

end RamanujanPetersson
