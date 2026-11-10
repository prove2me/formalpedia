-- Prove2me | Theorems.Thm_RobersonCx_lemma_10
-- name    : RobersonCx.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:52.243782+00:00
-- url     : https://prove2.me/theorems/41457989-5ca0-4d87-a56b-6333c3c7330e
-- title:
--   Lemma 10 — infinitely many primes $p\not\equiv\pm1\pmod r$
-- statement:
--   Let $r\ge2$ admit an integer $a$ with $\gcd(a,r)=1$ and $a\not\equiv\pm1\pmod r$. Then the set
--   $$P_r=\{p : p\text{ prime},\ \gcd(p,r)=1,\ p\not\equiv\pm1\pmod r\}$$
--   is infinite.
--
--   The primes of $P_r$ are the moduli $m=p$ for which Theorem 9 excludes the base graph from $D^{(r)}_{qp}$ and $B^{(r)}_{qp}$.
--
--   Differences from the source:
--   - encoding: congruences modulo $r$ → equalities of casts in `ZMod r`; reason: same instances
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), Lemma 10, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- Lemma 10 (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.2, p.10 (PDF p.12)). Let `r ≥ 2` admit an integer `a` with `gcd(a, r) = 1` and
`a ≢ ±1 (mod r)`. Then the set `P_r := {p : p is prime, gcd(p, r) = 1, p ≢ ±1 (mod r)}` is infinite.

**Formalization Note** Congruences mod `r` are equalities in `ZMod r`. -/
theorem lemma_10 (r : ℕ) (hr : 2 ≤ r)
    (ha : ∃ a : ℤ, Int.gcd a r = 1 ∧ (a : ZMod r) ≠ 1 ∧ (a : ZMod r) ≠ -1) :
    {p : ℕ | p.Prime ∧ Nat.Coprime p r ∧ (p : ZMod r) ≠ 1 ∧ (p : ZMod r) ≠ -1}.Infinite := by sorry

end RobersonCx
