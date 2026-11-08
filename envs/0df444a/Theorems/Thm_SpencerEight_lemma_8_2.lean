-- Prove2me | Theorems.Thm_SpencerEight_lemma_8_2
-- name    : SpencerEight.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:53.951252+00:00
-- url     : https://prove2.me/theorems/11a15e43-37fd-4fef-be66-ad39efa77e8c
-- title:
--   Lemma 8.2 — a peaked translated density
-- statement:
--   Let $Z$ have the density $f_Z$ with parameters $(s_\star,a_\star)$, let $\sigma$ be a uniform sign independent of $Z$, and let $P$ be the law of $Z+s_\star\sigma$. Then $P$ has an even density nonincreasing on $[0,\infty)$, and
--   $$P([-x,x])\ge\gamma_1([-x,x])\qquad(x\ge0).$$
--   Consequently, for every symmetric convex Borel set $K\subseteq\mathbb R^m$,
--   $$P^{\otimes m}(K)\ge\gamma_m(K).$$
--
--   This comparison is what converts Gaussian mass into a count of sign vectors.
--
--   Differences from the source:
--   - encoding: σ a uniform sign independent of Z → the image of the product of the law of Z and ½δ₁ + ½δ₋₁ under (z, σ) ↦ z + sσ; reason: the same law
--   - encoding: K symmetric, K = −K → x ∈ K → −x ∈ K; reason: equivalent
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.2, p.69 (PDF p.69)

import Mathlib
import Definitions.Def_SpencerEight_PeakedDensityComparison
import Definitions.Def_SpencerEight_sStar
import Definitions.Def_SpencerEight_aStar

namespace SpencerEight

/-- Lemma 8.2 (A peaked translated density), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.69 (PDF p.69). All three conclusions at `(s⋆, a⋆)`, with `b⋆ = (1 − 2s⋆a⋆)/s⋆²`. -/
theorem lemma_8_2 : PeakedDensityComparison sStar aStar := by sorry

end SpencerEight
