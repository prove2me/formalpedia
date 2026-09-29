-- Prove2me | Theorems.Thm_PrimePairSieve_squarefree_primitive_fourier_energy
-- name    : PrimePairSieve_squarefree_primitive_fourier_energy
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T18:18:54.465345+00:00
-- url     : https://prove2.me/theorems/9e02419f-6b64-4e1f-bafa-93f2120d65e4
-- title:
--   Primitive Fourier energy for the squarefree prime-pair sieve
-- statement:
--   Let $q\ge1$ be squarefree, let $d$ be an even nonnegative integer, and let $A$ be a finite set of nonnegative integers such that no prime divisor of $q$ divides $n(n+d)$ for any $n\in A$. Define
--   $$\rho_d(p)=\begin{cases}1,&p\mid d,\\2,&p\nmid d,\end{cases}\qquad
--    g_d(q)=\prod_{p\mid q}\frac{\rho_d(p)}{p-\rho_d(p)}.$$
--   Writing $e(t)=\exp(2\pi it)$, one has
--   $$g_d(q)|A|^2\le\sum_{\substack{0\le a<q\\(a,q)=1}}\left|\sum_{n\in A}e(an/q)\right|^2.$$
--   The hypothesis means that $A$ avoids the actual polynomial roots $0,-d$ modulo each prime divisor of $q$. The estimate supplies the arithmetic lower-energy input to a large-sieve upper bound for the sifted set. It does not impose a diameter bound on $A$: elements may repeat after reduction modulo $q$. For $q=1$ the empty product is one and the single zero frequency gives equality. The case $d=0$ is included. Evenness ensures there is only one forbidden residue at the prime two, so every denominator is positive.
--
--   Formalization Note: primitive frequencies are indexed by the units of $\mathbb Z/q\mathbb Z$, and Mathlib's standard additive character represents $e(an/q)$. This theorem does not assert the final all-range prime-pair counting estimate.
-- source:
--   Classical finite-Fourier lower-energy step in the large-sieve proof of an upper-bound sieve. Proof uses Mathlib finite character orthogonality, the Chinese remainder theorem, and Cauchy–Schwarz on the literal excluded residues. Intended arithmetic input to https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385, paired with the accepted nonuniform large sieve https://prove2.me/theorems/ee72dd79-89b1-4fab-8700-1074eec4cacc. Related interval sieve application: Riesel–Vaughan, On sums of primes, pp. 51–54, https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf. Known mathematics; no novelty or final counting claim.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Squarefree
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve_squarefree_primitive_fourier_energy
    (q : ℕ) [NeZero q] (d : ℕ) (hq : Squarefree q) (hd : 2 ∣ d)
    (A : Finset ℕ)
    (hA : ∀ n ∈ A, ∀ p ∈ q.primeFactors, ¬ p ∣ n*(n+d)) :
    (∏ p ∈ q.primeFactors,
      if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) * (A.card : ℝ)^2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A, ZMod.stdAddChar (u.val*(n : ZMod q))‖^2 := by sorry
