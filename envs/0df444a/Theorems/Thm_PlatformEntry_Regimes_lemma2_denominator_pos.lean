-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_lemma2_denominator_pos
-- name    : PlatformEntry.Regimes.lemma2_denominator_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:48.524794+00:00
-- url     : https://prove2.me/theorems/2d62a7a1-f5f8-493c-8a0c-c4f34005e5ed
-- title:
--   Proof of Lemma 2, PDF p. 32 — under (5), the denominator of e*_P and e*_P/(a+e_S) are positive
-- statement:
--   Let $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$ satisfy condition (5),
--   $$4(1+\delta) - 2\beta(2-\delta+\delta^2) + \beta^3(1+f) - \beta^2(2+f+\delta f) > 0 .$$
--   Then the denominator and the numerator of the platform's optimal effort per unit of carried-over value in Lemma 2 are both positive:
--
--   $$
--   D = 8 - 8\delta^2 f + 8\beta\delta(1+f) - 2\beta^3\delta f(1+f) + \beta^4(1+f)^2 + 2\beta^2(-4-3f+\delta^2(-1+f^2)) > 0,
--   $$
--   $$
--   8 + 8\delta f - 4\beta(1+\delta)(1+f) + \beta^3(1+\delta)f(1+f) - 2\beta^2(f+\delta(-1+f^2)) > 0 .
--   $$
--
--   This is the sentence "under condition (5), $e^*_P$ derived above is positive and optimal and its denominator is positive as well" of the proof of Lemma 2 (positivity part). It makes the quotient in $H$ of (8) well defined and $e^*_P > 0$ when $a + e_S > 0$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Lemma 2, PDF p. 32

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem lemma2_denominator_pos (δ f β : ℝ) (hbox : InBox δ f β) (h5 : cond5 δ f β) :
    0 < D δ f β ∧ 0 < ePNum δ f β := by sorry

end PlatformEntry.Regimes
