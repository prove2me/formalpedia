-- Prove2me | Theorems.Thm_SmolenskyAC_lemma_5
-- name    : SmolenskyAC.lemma_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:46:33.647581+00:00
-- url     : https://prove2.me/theorems/d51f2706-0483-4cfd-a998-c762ce7e2b20
-- title:
--   Lemma 5 — for distinct primes $p,q$ some field of characteristic $p$ has a $q$-th root of unity
-- statement:
--   Let $p$ and $q$ be distinct primes. Then there is a field $F$ of characteristic $p$ containing a $q$-th root of unity, i.e. an element $a\in F$ with $a\ne1$ and $a^q=1$.
--
--   It supplies the field in which $\mathrm{MOD}_p$ is easy and the $\mathrm{MOD}_{s,q}$ functions are complete.
--
--   Differences from the source: none.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Lemma 5, p.81 (pdf 5)

import Mathlib

namespace SmolenskyAC

/-- **Lemma 5** (Smolensky, STOC 1987, p.81): if `p` and `q` are two distinct primes then there is
a field of characteristic `p` which contains a `q`-th root of unity (an element `a ≠ 1` with
`a^q = 1`, Definition, p.80). -/
theorem lemma_5 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ (F : Type) (_ : Field F), CharP F p ∧ ∃ a : F, a ≠ 1 ∧ a ^ q = 1 := by sorry

end SmolenskyAC
