-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_lemma_4
-- name    : TeamDiversity.WageGap.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:11.023588+00:00
-- url     : https://prove2.me/theorems/7b1741b2-9a34-4cf0-a04c-c71de5162cac
-- title:
--   Lemma 4 (first sentence), p. 16 — if f_s(0)/f_s(2) > f_d(0)/f_d(2), then E[w_s**] − E[w_d*] > 0 for all δ
-- statement:
--   Assume the standing assumptions and $\frac{f_s(0)}{f_s(2)} > \frac{f_d(0)}{f_d(2)}$. Let $w_s^{**}(\delta)$ and $w_d^*(\delta)$ be the least feasible wages of the specialized program (with No-cycling) and of the diverse program. Then, for every $\delta \in [0,1]$,
--
--   $$E[w_s^{**}] - E[w_d^*] = f_s(2)\,w_s^{**}(\delta) - f_d(2)\,w_d^*(\delta) > 0.$$
--
--   With collusion taken into account, the expected wage is always higher under specialized assignment; this is the condition Proposition 2 assumes.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 16 (PDF 17), Lemma 4 (first sentence)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Lemma 4 (first sentence), p. 16: if `f_s(0)/f_s(2) > f_d(0)/f_d(2)`, then
`E[w_s**] − E[w_d*] > 0` for all `δ`. -/
theorem lemma_4 (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd)
    (hratio : fs.f0 / fs.f2 > fd.f0 / fd.f2) (ws wd : ℝ → ℝ)
    (hws : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasS c fs δ) (ws δ))
    (hwd : ∀ δ ∈ Set.Icc (0 : ℝ) 1, IsLeast (FeasD c fd δ) (wd δ)) :
    ∀ δ ∈ Set.Icc (0 : ℝ) 1, expWage fs (ws δ) - expWage fd (wd δ) > 0 := by sorry

end TeamDiversity.WageGap
