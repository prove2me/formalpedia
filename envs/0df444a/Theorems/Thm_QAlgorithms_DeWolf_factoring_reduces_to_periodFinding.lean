-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_factoring_reduces_to_periodFinding
-- name    : QAlgorithms.DeWolf.factoring_reduces_to_periodFinding
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:42:06.134952+00:00
-- url     : https://prove2.me/theorems/878b04c9-9196-4300-83ec-cf44cf8f124e
-- title:
--   Factoring reduces to period finding: the number-theoretic core of Shor's reduction
-- statement:
--   Let $N>1$ be an odd integer that is not a prime power (so $N$ is composite and not of the form $p^k$, $k\ge1$). For an integer $x$ coprime to $N$, let $r=\operatorname{ord}_N(x)$ be its period: the least integer $r>0$ with $x^r\equiv1\pmod N$. Then the following hold.
--
--   1. If $x\in\{2,\dots,N-1\}$ is not coprime to $N$, then $1<\gcd(x,N)<N$.
--   2. If $x$ is coprime to $N$, then $0<r\le N$, and $r$ is the period of modular exponentiation $f(a)=x^a\bmod N$: for all $a,b\in\mathbb N$, $f(a)=f(b)$ if and only if $a\equiv b\pmod r$.
--   3. If $x\in\{2,\dots,N-1\}$ is coprime to $N$, $r$ is even, and $N$ divides neither $x^{r/2}+1$ nor $x^{r/2}-1$, then
--
--   $$
--   1<\gcd\big(x^{r/2}+1,N\big)<N \qquad\text{and}\qquad 1<\gcd\big(x^{r/2}-1,N\big)<N .
--   $$
--
--   4. If $x$ is chosen uniformly from $\{2,\dots,N-1\}$, then conditioned on $x$ being coprime to $N$, the probability that $r$ is even and $N\nmid x^{r/2}\pm1$ is at least $1/2$:
--
--   $$
--   \#\{x\in\{2,\dots,N-1\}:\gcd(x,N)=1\}\;\le\;2\cdot\#\{x\in\{2,\dots,N-1\}:\gcd(x,N)=1,\ r\text{ even},\ N\nmid x^{r/2}+1,\ N\nmid x^{r/2}-1\}.
--   $$
--
--   Together these show that an efficient algorithm for finding the period of $a\mapsto x^a\bmod N$ yields an efficient randomized algorithm for finding a nontrivial factor of $N$; this is the classical half of Shor's factoring algorithm.
--
--   **Formalization Note** The period is Mathlib's `orderOf` of $x$ in the ring $\mathbb Z/N\mathbb Z$, i.e. the least positive exponent with $x^r=1$. The power $x^{r/2}$ and the difference $x^{r/2}-1$ are computed in $\mathbb N$; since $x\ge2$ and $r/2\ge1$ the subtraction never truncates. "Not a prime power" is Mathlib's `IsPrimePow`, which counts primes as prime powers.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 49, §5.2. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Fourier
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf §5.2, PDF pp.49–50 (unnumbered): the number-theoretic core of the reduction from
factoring to period-finding. Let `N > 1` be odd and not a prime power (in particular composite;
p.49), and pick `x ∈ {2, …, N − 1}`. Then:

1. if `x` is not coprime to `N`, then `gcd(x, N)` is a nontrivial factor of `N`;
2. if `x` is coprime to `N`, its period `r` (the least `0 < r ≤ N` with `x^r ≡ 1 mod N`) is the
   period of `f(a) = x^a mod N`, i.e. `f(a) = f(b)` iff `a ≡ b (mod r)`;
3. if moreover `r` is even and `N` divides neither `x^{r/2} + 1` nor `x^{r/2} − 1`, then both
   `gcd(x^{r/2} + 1, N)` and `gcd(x^{r/2} − 1, N)` are nontrivial factors of `N`;
4. for `x` uniform in `{2, …, N − 1}` and conditioned on `x` coprime to `N`, the event
   "`r` even, `N ∤ x^{r/2} + 1`, `N ∤ x^{r/2} − 1`" has probability `≥ 1/2`
   (cited to Nielsen–Chuang Thm A4.13), stated as `2 · #good ≥ #coprime`. -/
theorem factoring_reduces_to_periodFinding (N : ℕ) (hN : 1 < N) (hodd : Odd N)
    (hpp : ¬ IsPrimePow N) :
    (∀ x ∈ Finset.Icc 2 (N - 1), ¬ Nat.Coprime x N → 1 < Nat.gcd x N ∧ Nat.gcd x N < N) ∧
    (∀ x : ℕ, Nat.Coprime x N →
      0 < orderOf (x : ZMod N) ∧ orderOf (x : ZMod N) ≤ N ∧
        HasPeriod (fun a => x ^ a % N) (orderOf (x : ZMod N))) ∧
    (∀ x ∈ Finset.Icc 2 (N - 1), Nat.Coprime x N → Even (orderOf (x : ZMod N)) →
      ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 → ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1 →
        (1 < Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) + 1) N ∧
          Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) + 1) N < N) ∧
        (1 < Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) - 1) N ∧
          Nat.gcd (x ^ (orderOf (x : ZMod N) / 2) - 1) N < N)) ∧
    ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N).card ≤
      2 * ((Finset.Icc 2 (N - 1)).filter fun x => Nat.Coprime x N ∧
        Even (orderOf (x : ZMod N)) ∧ ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) + 1 ∧
        ¬ N ∣ x ^ (orderOf (x : ZMod N) / 2) - 1).card := by
  sorry


end QAlgorithms.DeWolf
