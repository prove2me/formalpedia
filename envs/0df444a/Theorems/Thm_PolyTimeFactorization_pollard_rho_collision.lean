-- Prove2me | Theorems.Thm_PolyTimeFactorization_pollard_rho_collision
-- name    : PolyTimeFactorization.pollard_rho_collision
-- status  : Proved
-- author  : @Lucas
-- created : 2026-11-16T16:13:10.678217+00:00
-- url     : https://prove2.me/theorems/187a599d-fd77-4de0-affe-c2ae75d8ac0f
-- title:
--   Pollard's rho: the collision lemma
-- statement:
--   The collision lemma behind Pollard's rho method. Let $p$ be a prime properly dividing the composite $n$ (so $p<n$), and let $x,y\in\mathbb{Z}$ satisfy $x\equiv y\pmod p$ but $x\not\equiv y\pmod n$. Then
--   $$1<\gcd(x-y,\,n)<n,$$
--   so the gcd yields a nontrivial factor of $n$.
--
--   In the rho method the iterates of a polynomial modulo $n$ eventually collide modulo $p$ — heuristically after $O(\sqrt{p})$ steps, by the birthday paradox — while remaining distinct modulo $n$. This lemma is the rigorous step that converts such a collision into a factor.
-- source:
--   J. M. Pollard, A Monte Carlo method for factorization, BIT 15 (1975), 331-334 (the gcd step of the rho method), https://doi.org/10.1007/BF01933667

import Mathlib

namespace PolyTimeFactorization

theorem pollard_rho_collision (n p : ℕ) (x y : ℤ) (hp : p.Prime) (hpn : p ∣ n)
    (hlt : p < n) (hcol : (p : ℤ) ∣ x - y) (hncol : ¬ (n : ℤ) ∣ x - y) :
    1 < Int.gcd (x - y) (n : ℤ) ∧ Int.gcd (x - y) (n : ℤ) < n := by sorry

end PolyTimeFactorization
