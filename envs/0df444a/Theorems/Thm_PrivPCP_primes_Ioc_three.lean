-- Prove2me | Theorems.Thm_PrivPCP_primes_Ioc_three
-- name    : PrivPCP.primes_Ioc_three
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:08:07.950137+00:00
-- url     : https://prove2.me/theorems/809c49b3-fc9c-5f10-9f5c-e1978d5f99e3
-- title:
--   At least $t$ primes in $(m,3m]$ for $m\ge A_0t\log(t+1)$
-- statement:
--   This is a Chebyshev-type estimate for primes in intervals of the form $(m,3m]$.
--
--   There is an absolute constant $A_0>0$ such that for every integer $t\ge1$ and every integer $m$ with
--   $$m\ \ge\ A_0\,t\log(t+1),$$
--   the interval $(m,3m]$ contains at least $t$ primes.
--
--   The proof of Lemma 5.4 in the source needs a supply of many distinct primes of a prescribed size, so that the side lengths $s_i=b_ih_i$ can be chosen pairwise coprime and balanced. The source uses intervals $(x,2x)$ and the prime number theorem. Intervals $(m,3m]$ already follow from Chebyshev's elementary bounds: $\vartheta(3m)-\vartheta(m)\ge m\log2-O(\sqrt m\log m)$, by $\psi(n)\ge n\log2-\log(n+1)$ and $\vartheta(x)\le x\log4$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The primes are counted as the cardinality of the set of primes in `Finset.Ioc m (3 * m)`.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), proof of Lemma 5.4, p.29 (PDF p.31): prime supply 'for every integer t >= 1 and every real x >= A0 t log(t+1), the interval (x, 2x) contains at least t primes'; here with (m, 3m], which follows from Chebyshev's bounds (Mathlib: Chebyshev.theta_ge, Chebyshev.theta_le_log4_mul_x)

import Mathlib

namespace PrivPCP

theorem primes_Ioc_three : ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ t : ℕ, 1 ≤ t → ∀ m : ℕ,
    A₀ * t * Real.log (t + 1) ≤ m → t ≤ ((Finset.Ioc m (3 * m)).filter Nat.Prime).card := by sorry

end PrivPCP
