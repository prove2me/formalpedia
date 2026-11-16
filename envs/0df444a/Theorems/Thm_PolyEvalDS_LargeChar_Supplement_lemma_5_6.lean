-- Prove2me | Theorems.Thm_PolyEvalDS_LargeChar_Supplement_lemma_5_6
-- name    : PolyEvalDS.LargeChar.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:57:43.87652+00:00
-- url     : https://prove2.me/theorems/0c1a6ee3-1ddf-4acb-bd0d-398933b99b1b
-- title:
--   Lemma 5.6 — $|\mathrm{Res}(g,h)|\le(d+1)^{3d/2}$ for a divisor $h$ of a $\{-1,0,1\}$-polynomial
-- statement:
--   Let $d\ge 0$ be an integer and let $f,g\in\mathbb Z[X]$ be polynomials of degree at most $d$ with every coefficient in $\{-1,0,1\}$, where $f\neq 0$ ($g$ may be zero). Let $h\in\mathbb Z[X]$ be any divisor of $f$ in $\mathbb Z[X]$. Then the resultant of $g$ and $h$ satisfies
--
--   $$
--   |\operatorname{Res}(g,h)|\le (d+1)^{3d/2}.
--   $$
--
--   Here $\operatorname{Res}(g,h)$ is the determinant of the Sylvester matrix of $g$ and $h$ taken with respect to their actual degrees $\deg g$ and $\deg h$; it is an integer, and the exponent $3d/2$ is a real number (not an integer when $d$ is odd).
--
--   This bound is the arithmetic input of Lemma 5.7: when a prime $p$ exceeds $(d+1)^{3d/2}$, a resultant of this shape cannot vanish modulo $p$ unless it vanishes over $\mathbb Z$.
--
--   **Formalization Note** The resultant is Mathlib's `Polynomial.resultant g h` with its default size parameters `g.natDegree` and `h.natDegree`; padded degrees are not used.
--
--   Differences from the source:
--   - generalization: d the degree bound of §5, a positive integer → d : ℕ, so d = 0 is included; reason: the statement at d = 0 is the same claim for constant polynomials and is true; for d ≥ 1 the Lean statement is exactly the source's
--   - encoding: Res(g, h) → Polynomial.resultant g h, whose size parameters default to g.natDegree and h.natDegree; reason: the Sylvester determinant with respect to the actual degrees is the resultant of the source; for g = 0 or constant h it takes its standard value
--   - encoding: (d+1)^{3d/2} → ((d:ℝ)+1) ^ ((3*(d:ℝ))/2), a real power; reason: 3d/2 is not an integer for odd d; the real power is the printed value
--   - encoding: coefficients in {−1, 0, 1}, degree at most d → ∀ i, coeff i ∈ {−1, 0, 1} and natDegree ≤ d; reason: the coefficients of index above d are 0 automatically; natDegree 0 = 0 ≤ d matches degree(0) = −∞
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Lemma 5.6, p. 12 (proof p. 12)

import Mathlib
open Polynomial

namespace PolyEvalDS.LargeChar.Supplement

/-- Lemma 5.6, p. 12 (Okada, Player, Pohmann, STOC 2027 submission #463, October 2026).
Let `f, g ∈ ℤ[X]`, `f ≠ 0`, have coefficients in `{-1, 0, 1}` and degree at most `d`, and let
`h ∈ ℤ[X]` divide `f`. Then `|Res(g, h)| ≤ (d + 1)^(3d/2)`.
`Res(g, h)` is Mathlib's `resultant g h` with its default size parameters, the actual degrees
`g.natDegree` and `h.natDegree` (the Sylvester determinant). The exponent `3d/2` is a real power. -/
theorem lemma_5_6 (d : ℕ) (f g h : ℤ[X]) (hf0 : f ≠ 0)
    (hf_deg : f.natDegree ≤ d) (hg_deg : g.natDegree ≤ d)
    (hf_coeff : ∀ i, f.coeff i ∈ ({-1, 0, 1} : Set ℤ))
    (hg_coeff : ∀ i, g.coeff i ∈ ({-1, 0, 1} : Set ℤ))
    (hhf : h ∣ f) :
    ((|resultant g h| : ℤ) : ℝ) ≤ ((d : ℝ) + 1) ^ ((3 * (d : ℝ)) / 2) := by sorry

end PolyEvalDS.LargeChar.Supplement
