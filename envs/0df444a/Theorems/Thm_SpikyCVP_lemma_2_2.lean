-- Prove2me | Theorems.Thm_SpikyCVP_lemma_2_2
-- name    : SpikyCVP.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:43:44.089975+00:00
-- url     : https://prove2.me/theorems/c4bd4bc0-e6c8-423c-86bb-18066d652be3
-- title:
--   Lemma 2.2 — the $J_\tau$ inequality
-- statement:
--   Let $0<\tau\le 1/2$ and $1<p<2$. For $a,b\in\mathbb R$ let $J_\tau(a,b)=((1-\tau)a^2+\tau b^2)^{p/2}-(1-\tau)|a|^p-\tau|b|^p$. Then
--
--   $$J_\tau(a,b)\le\frac{64}{p-1}\,\tau^{p/2}\Big(\frac{|a|^p+|b|^p}{2}-\Big|\frac{a+b}{2}\Big|^p\Big).\qquad(2.1)$$
--
--   This is where $p>1$ is needed: it bounds the loss of the quadratic relaxation by the midpoint convexity gap of $|z|^p$, which is what makes two posteriors overlap in Lemma 4.4.
--
--   Differences from the source: none.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.2, Equation (2.1), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SpikyCVP_Jtau

namespace SpikyCVP

/-- **Lemma 2.2 (the `Jτ` inequality).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.2, p.11 (PDF p.13).

Let `0 < τ ≤ 1/2` and `1 < p < 2`. For `a, b ∈ ℝ`,
`Jτ(a, b) ≤ (64/(p − 1)) τ^{p/2} ((|a|^p + |b|^p)/2 − |(a + b)/2|^p)`  (2.1). -/
theorem lemma_2_2 (τ p a b : ℝ) (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) (hp1 : 1 < p) (hp2 : p < 2) :
    Jtau τ p a b ≤
      64 / (p - 1) * τ ^ (p / 2) * ((|a| ^ p + |b| ^ p) / 2 - |(a + b) / 2| ^ p) := by sorry

end SpikyCVP
