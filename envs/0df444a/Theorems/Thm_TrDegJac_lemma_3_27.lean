-- Prove2me | Theorems.Thm_TrDegJac_lemma_3_27
-- name    : TrDegJac.lemma_3_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:57.562255+00:00
-- url     : https://prove2.me/theorems/ecaa3568-11fb-4d46-9a6d-8fc04f387944
-- title:
--   Lemma 3.27 — $\binom{n+B}{n}\cdot\frac ab>\binom{n+B+d'}{n}$ for large $B$
-- statement:
--   Let $n,d',a,b\in\mathbb N$ with $a>b$. Then for all sufficiently large $B\in\mathbb N$,
--   $$
--   b\cdot\binom{n+B+d'}{n}\ <\ a\cdot\binom{n+B}{n},
--   $$
--   that is, $\binom{n+B}{n}\cdot\frac ab>\binom{n+B+d'}{n}$ when $b\ge1$.
--
--   The lemma is what makes $\dim V>\dim W$ in Lemma 3.22 achievable in the proof of Proposition 3.30.
--
--   Differences from the source:
--   - encoding: (n+B choose n) · a/b > (n+B+d′ choose n), for sufficiently large B → b · (n+B+d′ choose n) < a · (n+B choose n) in ℕ, for all B ≥ B₀ for some B₀; reason: multiplying by b > 0 changes no instance; 'sufficiently large' is eventually
--   - generalization: b with a/b defined (b ≥ 1) → also b = 0; reason: at b = 0 the multiplied-out inequality says 0 < a · (n+B choose n), which holds since a > 0; for b ≥ 1 it is the printed inequality
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 3.27, p.19

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Lemma 3.27** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.19:
"Let n, d′, a, b ∈ N be fixed, for sufficiently large B we have that (n+B choose n) · a/b >
(n+B+d′ choose n) provided that a > b."

**Formalization Note.** The inequality is multiplied out by `b`:
`b · \binom{n+B+d′}{n} < a · \binom{n+B}{n}`, in `ℕ`. For `b ≥ 1` this is the printed inequality; at
`b = 0`, where `a/b` is undefined, it still holds (`a > 0`). "For sufficiently large `B`" is
`∃ B₀, ∀ B ≥ B₀`. -/
theorem lemma_3_27 (n d' a b : ℕ) (hab : b < a) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, b * (n + B + d').choose n < a * (n + B).choose n := by sorry

end TrDegJac
