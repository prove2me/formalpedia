-- Prove2me | Theorems.Thm_RiskyBenefitCost_NthDegree_argmax_nonempty
-- name    : RiskyBenefitCost.NthDegree.argmax_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:20.14168+00:00
-- url     : https://prove2.me/theorems/440c80d4-bffe-4466-aee1-92919706537e
-- title:
--   §4, p. 3627 (PDF 4) — the maximizer sets B∗ᵢ of (4) are nonempty
-- statement:
--   Let $0\le\underline x<\bar x$ and let $\tilde X$ have a law $\mu$ concentrated on $[\underline x,\bar x]$. Let $B\subset\mathbb R$ be nonempty and compact, $f$ continuous on $B$, and $U$ continuous and increasing. Then the maximizer set
--   $$B^*=\operatorname*{argmax}_{b\in B}\ \mathbb E\,U\big(f(b)(\tilde X-x_0)+z_0\big)$$
--   of display (4) is nonempty.
--
--   This is what keeps the strong-set-order comparisons of Lemma 3 and Proposition 2 from holding vacuously.
--
--   **Formalization Note.** Nonemptiness of $B$ is added: the page leaves it implicit (a maximization over the empty set has no solution). Only continuity of $U$ is used from "sufficiently differentiable".
-- source:
--   Menegatti & Peter, Changes in risky benefits and in risky costs: a question of the right order, Management Science 68(5) (2022), p. 3627 (PDF 4), §4, sentence after display (4)

import Mathlib
import Definitions.Def_RiskyBenefitCost_NthDegree_Model

namespace RiskyBenefitCost.NthDegree
open MeasureTheory ProbabilityTheory

theorem argmax_nonempty (xl xu x0 z0 : ℝ) (hxl : 0 ≤ xl) (hlt : xl < xu)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Icc xl xu)ᶜ = 0)
    (B : Set ℝ) (hB : IsCompact B) (hBne : B.Nonempty) (f : ℝ → ℝ) (hf : ContinuousOn f B)
    (U : ℝ → ℝ) (hU : Continuous U) (hUmono : Monotone U) :
    (argmaxSet B (EU U f x0 z0 μ)).Nonempty := by sorry

end RiskyBenefitCost.NthDegree
