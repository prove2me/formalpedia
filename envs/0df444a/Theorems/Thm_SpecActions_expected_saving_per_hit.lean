-- Prove2me | Theorems.Thm_SpecActions_expected_saving_per_hit
-- name    : SpecActions.expected_saving_per_hit
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:42:30.628577+00:00
-- url     : https://prove2.me/theorems/611f0093-5d14-441d-83fb-dc10a8484a6b
-- title:
--   Expected time saved per hit: $\mathbb{E}[(B-A)^+]=\frac{\alpha}{\beta(\alpha+\beta)}$
-- statement:
--   Let $A\sim\mathrm{Exp}(\alpha)$ be the speculator's latency and $B\sim\mathrm{Exp}(\beta)$ the real API call's latency, independent. When a guess is correct the block of two consecutive steps finishes at $C+\min\{A,B\}$ instead of $B+C$, so the time saved is $(B-A)^+$. Its expectation is
--
--   $$\mathbb{E}\bigl[(B-A)^+\bigr]=\int_0^\infty\!\!\int_0^b (b-a)\,\alpha e^{-\alpha a}\,\beta e^{-\beta b}\,da\,db=\frac{\alpha}{\beta(\alpha+\beta)}$$
--
--   for all $\alpha,\beta>0$. The statement is the iterated integral against the two exponential densities; since the asserted value is strictly positive, a proof must establish integrability rather than appeal to the convention that a non-integrable integral is zero.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Appendix A (p. 13), the computation of $\mathbb{E}[(B-A)^+]=\alpha/(\beta(\alpha+\beta))$

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace SpecActions
theorem expected_saving_per_hit (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∫ b in Set.Ioi (0:ℝ),
        (∫ a in (0:ℝ)..b, (b - a) * (α * Real.exp (-α * a)))
          * (β * Real.exp (-β * b))
      = α / (β * (α + β)) := by sorry
end SpecActions
