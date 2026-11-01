-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_lemma_10_8_1
-- name    : WildeQIT.PinskerRefined.lemma_10_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:09.197741+00:00
-- url     : https://prove2.me/theorems/41f4d67b-90d2-489b-81b8-65256b7a7a00
-- title:
--   Lemma 10.8.1 — $a\ln\frac ab+(1-a)\ln\frac{1-a}{1-b}\ge 2(a-b)^2$
-- statement:
--   Let $a,b\in[0,1]$. Then
--
--   $$
--   a\ln\frac ab+(1-a)\ln\frac{1-a}{1-b}\ge 2(a-b)^2 .
--   $$
--
--   The left side is the binary relative entropy of $(a,1-a)$ with respect to $(b,1-b)$ in nats, with the conventions $0\ln(0/c)=0$ and $c\ln(c/0)=+\infty$ for $c>0$; for $b\in\{0,1\}$ and $a\ne b$ it is $+\infty$ and the inequality holds trivially, as the book notes. This is the two-point case of Pinsker's inequality, to which the general case is reduced by a coarse-graining channel.
--
--   **Formalization Note** The left side is written as $\ln 2\cdot D(p\|q)$ with the published `relEntropy` (bits, extended reals, $+\infty$ off support) on the two-point alphabet `Fin 2`, where $p=(a,1-a)$ is an arbitrary probability distribution on `Fin 2` (so $a=p(0)$ ranges over $[0,1]$) and $q=(b,1-b)$.
--
--   Differences from the source:
--
--   - encoding: a ln(a/b) + (1 − a) ln((1 − a)/(1 − b)) for a, b ∈ [0, 1], +∞ when b ∈ {0, 1} and a ≠ b → ln 2 · relEntropy p ![b, 1 − b] in EReal, with p any FinDist on Fin 2 and a = p(0); reason: relEntropy carries the book’s support convention (Definition 10.5.2) so the endpoints b ∈ {0, 1} keep their extended values; ln 2 converts bits to nats; every a ∈ [0, 1] is p(0) for p = (a, 1 − a)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 10.8.1, p. 311

import Definitions.Def_WildeQIT_relEntropy

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Lemma 10.8.1**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 311: for `a, b ∈ [0, 1]`,
`a ln(a/b) + (1 − a) ln((1 − a)/(1 − b)) ≥ 2 (a − b)²`.

**Formalization Note** The left side is the binary relative entropy in nats, with the book's
conventions at `b ∈ {0, 1}` (`0 ln(0/·) = 0`, and `+∞` when `a ≠ b = 0` or `a ≠ b = 1`, the case the
book calls trivial). It is stated as `ln 2 · D(p‖q)` with the published `relEntropy` (bits, `EReal`,
`+∞` off support, Definition 10.5.2) on the two-point alphabet `Fin 2`, where `p = (a, 1 − a)` is any
probability distribution on `Fin 2` (`a = p(0)`, so `a` ranges over all of `[0, 1]`) and
`q = (b, 1 − b)`. In `EReal`, `ln 2 · (+∞) = +∞`. -/
theorem lemma_10_8_1 (p : FinDist (Fin 2)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ((2 * (p.prob 0 - b) ^ 2 : ℝ) : EReal) ≤
      ((Real.log 2 : ℝ) : EReal) * relEntropy p ![b, 1 - b] := by sorry

end WildeQIT.PinskerRefined
