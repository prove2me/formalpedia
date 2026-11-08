-- Prove2me | Theorems.Thm_SpikyCVP_lemma_2_5
-- name    : SpikyCVP.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:46:18.660074+00:00
-- url     : https://prove2.me/theorems/9cf77cdc-8e56-4270-a7a3-7bb751f4b6ef
-- title:
--   Lemma 2.5 — tilt bound on $g_\alpha$
-- statement:
--   Let $0<\alpha<1$, $q=\alpha/(1-\alpha)$, $\kappa_p=(1-\alpha)\alpha^q$ and $\beta=2^{1/q}$, and let $g_\alpha$ be the density of Equation (2.11). For every $a>0$,
--
--   $$g_\alpha(a)\exp\Big(\frac{\kappa_p a^{-q}}{2}\Big)\le 2\beta\, g_\alpha(\beta a).$$
--
--   It controls the exponential moment of the gap between $|z|^p$ and its quadratic majorant (Claim 4.3).
--
--   Differences from the source: none.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.5, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_SpikyCVP_gStable

namespace SpikyCVP

/-- **Lemma 2.5 (tilt bound on `gα`).**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Lemma 2.5, p.14 (PDF p.16).

Let `0 < α < 1` (`α = p/2`, §2.2), `q = α/(1 − α)`, `κp = (1 − α)α^q`, `β = 2^{1/q}`. For `a > 0`,
`gα(a) exp(κp a^{−q}/2) ≤ 2β gα(βa)`. -/
theorem lemma_2_5 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (a : ℝ) (ha : 0 < a) :
    gStable α a * Real.exp (kappa α * a ^ (-qExp α) / 2) ≤
      2 * betaC α * gStable α (betaC α * a) := by sorry

end SpikyCVP
