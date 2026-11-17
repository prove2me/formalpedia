-- Prove2me | Theorems.Thm_PolyTimeFactorization_pollard_p_minus_one
-- name    : PolyTimeFactorization.pollard_p_minus_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T16:12:58.371624+00:00
-- url     : https://prove2.me/theorems/ebb25f47-ee96-4496-b3e6-44f7998ada4b
-- title:
--   Pollard's $p-1$ criterion
-- statement:
--   Pollard's $p-1$ criterion. Let $p$ be a prime dividing $n$, let $a\ge 2$ with $p\nmid a$, and let $B\ge 1$. Put $M=\mathrm{lcm}(1,2,\dots,B)$. If $p-1$ divides $M$ — equivalently, $p-1$ is $B$-power-smooth, meaning every prime power $q^e\mid p-1$ satisfies $q^e\le B$ — then
--   $$p\mid\gcd(a^M-1,\,n).$$
--
--   Thus a single modular exponentiation $a^M\bmod n$ followed by a gcd reveals the factor $p$, provided $p-1$ is sufficiently smooth. This is the correctness guarantee of Pollard's $p-1$ method and follows from Fermat's little theorem. The hypothesis concerns $p-1$, not $n-1$.
-- source:
--   J. M. Pollard, Theorems on factorization and primality testing, Math. Proc. Cambridge Philos. Soc. 76 (1974), 521-528 (the p-1 method), https://doi.org/10.1017/S0305004100049252 ; standard formulation: https://en.wikipedia.org/wiki/Pollard%27s_p_%E2%88%92_1_algorithm

import Mathlib

namespace PolyTimeFactorization

theorem pollard_p_minus_one (n p a B : ℕ) (hp : p.Prime) (hpn : p ∣ n)
    (ha : 1 < a) (hpa : ¬ p ∣ a) (hB : 1 ≤ B)
    (hsmooth : p - 1 ∣ (Finset.Icc 1 B).lcm id) :
    p ∣ Nat.gcd (a ^ (Finset.Icc 1 B).lcm id - 1) n := by sorry

end PolyTimeFactorization
