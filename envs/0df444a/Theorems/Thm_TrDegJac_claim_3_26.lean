-- Prove2me | Theorems.Thm_TrDegJac_claim_3_26
-- name    : TrDegJac.claim_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:45.484524+00:00
-- url     : https://prove2.me/theorems/3351a733-7e20-4ebd-8947-e32cb9c4a61e
-- title:
--   Claim 3.26 — at least $\binom{n+N}{n}/\prod_i w_i$ monomials of weighted degree $\le N$
-- statement:
--   Let $n,N\in\mathbb N$ and let $w=(w_1,\dots,w_n)\in\mathbb N^n$ with every $w_i\ge1$. The $w$-weighted degree of a monomial $x^a=x_1^{a_1}\cdots x_n^{a_n}$ is $\sum_i w_ia_i$. Then
--   $$
--   \#\Big\{a\in\mathbb N^n:\ \sum_{i=1}^n w_ia_i\le N\Big\}\ \ge\ \frac{\binom{n+N}{n}}{\prod_{i=1}^n w_i}.
--   $$
--
--   The bound is used with $w_i=\deg f_i$ to show that the space of candidate annihilators is large (Lemma 3.28, Proposition 3.30).
--
--   **Formalization Note** Monomials are identified with their exponent vectors; the count is `Set.ncard` and the inequality is in $\mathbb Q$. The printed proof ends with "$|B|\le$", a misprint for "$\ge$"; the statement is unaffected.
--
--   Differences from the source:
--   - encoding: w ∈ ℕⁿ → w : Fin n → ℕ with 1 ≤ w i for every i; reason: at w_i = 0 the product ∏ w_i is 0 and the printed quotient is undefined; every use in the paper has w_i = deg f_i ≥ 1
--   - encoding: the number of monomials x^a → Set.ncard of the set of exponent vectors a : Fin n → ℕ; reason: monomials correspond bijectively to exponent vectors, and the set is finite since every w_i ≥ 1
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Claim 3.26, p.19 (w-weighted degree: §2.1, p.7)

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **Claim 3.26** — Forbes and Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027
submission (manuscript sha256 3ab72a42…), p.19:
"There are at least (n+N choose n)/(∏_i w_i) monomials x^a of w-weighted degree at most N."

For a weight vector `w ∈ ℕⁿ` (§2.1, p.7: "the w-weighted degree of x^a is ∑_{i=1}^n w_i a_i"),
the number of exponent vectors `a ∈ ℕⁿ` with `∑_i w_i a_i ≤ N` is at least
`\binom{n+N}{n} / ∏_i w_i`.

**Formalization Note.** Monomials `x^a` are identified with exponent vectors `a : Fin n → ℕ`; the
count is `Set.ncard`, and the set is finite because every `w_i ≥ 1`. The hypothesis `1 ≤ w i` excludes
`w_i = 0`, where `∏ w_i = 0` and the printed quotient is undefined; every use in the paper has
`w_i = deg f_i ≥ 1`. The inequality is in `ℚ`. (The printed proof ends with "|B| ≤", a misprint for
"≥"; the statement is unaffected.) -/
theorem claim_3_26 (n N : ℕ) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) :
    ((n + N).choose n : ℚ) / ∏ i, (w i : ℚ) ≤
      ({a : Fin n → ℕ | ∑ i, w i * a i ≤ N}.ncard : ℚ) := by sorry

end TrDegJac
