-- Prove2me | Theorems.Thm_RGMISFast_binomial_moment_exponential_tail
-- name    : RGMISFast.binomial_moment_exponential_tail
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T23:38:47.835219+00:00
-- url     : https://prove2.me/theorems/d52b9eed-23d1-4abf-b506-e4b07fe8b59e
-- title:
--   Exponential tail from geometric binomial moments
-- statement:
--   Let $K$ be a natural-valued random variable on a measure space, and let $C\ge1$. Assume for every integer $k\ge1$ that $\binom Kk$ is measurable and
--   $$\int\binom Kk\,d\mu\le (2eC)^k.$$
--   Then for every real $x\ge1$,
--   $$\mu\{K>32Cx\}\le e^{-x}.$$
--   This is the graph-independent moment-to-tail implication used for Equation (27). No probability-measure assumption is needed: the hypothesis on the positive-order binomial moments suffices. The source applies it with $C=c^{1+m-i}$.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §6.1, Lemma 6.1 proof: Equations (24)–(25), printed p.23, and tail bounds paragraph proving Equation (27), printed p.24 (PDF pp.25–26).

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.binomial_moment_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Measurable (fun ω => (K ω).choose k) ∧
      ∫⁻ ω, ((K ω).choose k : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal ((2*Real.exp 1*C)^k))
    (x : ℝ) (hx : 1 ≤ x) :
    μ {ω | 32*C*x < (K ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by sorry
