-- Prove2me | Theorems.Thm_PPDifferentiation_Costless_lemma_1_prisoners_dilemma
-- name    : PPDifferentiation.Costless.lemma_1_prisoners_dilemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:01.196471+00:00
-- url     : https://prove2.me/theorems/a7f015c0-0468-4a02-90a0-fd709868faf7
-- title:
--   Lemma 1, p. 10 — for 2(5 − 3√2)/7 < x_A + x_B < 2(2 + 3√2)/7 both firms earn less with PP than without it
-- statement:
--   Let $t>0$ and $x_A<x_B$ with
--   $$\frac{2(5-3\sqrt2)}{7}<x_A+x_B<\frac{2(2+3\sqrt2)}{7}.$$
--   Then a uniform-price equilibrium exists when neither firm implements PP, and at every such equilibrium $(p_A,p_B)$ both firms earn strictly less when both implement PP than when neither does:
--   $$\pi^{PP}_t(x_A,x_B)<\pi_A(p_A,p_B),\qquad \pi^{PP}_t(x_B,x_A)<\pi_B(p_A,p_B).$$
--
--   Together with the strict dominance of PP in the first part of Lemma 1 (the band lies inside $0<x_A+x_B<2$), this is the prisoner's dilemma of Lemma 1: the firms cannot help but implement PP, yet they would both be better off without it.
--
--   **Formalization Note** The strict order $x_A<x_B$ replaces the page's $x_A\le x_B$: at $x_A=x_B$ every profit is $0$ and "lower" fails. The "cannot help but implement PP" half is the separate dominance statement and is not restated here.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), p. 10, Lemma 1 (second part)

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

namespace PPDifferentiation.Costless

theorem lemma_1_prisoners_dilemma (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA < xB)
    (hlo : 2 * (5 - 3 * Real.sqrt 2) / 7 < xA + xB)
    (hhi : xA + xB < 2 * (2 + 3 * Real.sqrt 2) / 7) :
    (∃ pA pB : ℝ, IsPriceNE t xA xB pA pB) ∧
    ∀ pA pB : ℝ, IsPriceNE t xA xB pA pB →
      profPP t xA xB < uProf t xA xB pA pB ∧ profPP t xB xA < uProf t xB xA pB pA := by sorry

end PPDifferentiation.Costless
