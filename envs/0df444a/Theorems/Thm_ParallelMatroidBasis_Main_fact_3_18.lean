-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_fact_3_18
-- name    : ParallelMatroidBasis.Main.fact_3_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:07.639866+00:00
-- url     : https://prove2.me/theorems/ee14fa19-1699-45ff-a9d8-9e7aa944168d
-- title:
--   Fact 3.18 — Bernoulli KL divergence: $d_{KL}(\alpha\|\beta)\le\log_2(e)\frac{(\alpha-\beta)^2}{\beta(1-\beta)}$
-- statement:
--   For $\alpha\in[0,1]$ and $\beta\in(0,1)$, let $d_{KL}(\alpha\|\beta)$ be the base-2 KL divergence between the Bernoulli distributions with success probabilities $\alpha$ and $\beta$. Then
--   $$d_{KL}(\alpha\|\beta)\ \le\ \log_2(e)\,\frac{(\alpha-\beta)^2}{\beta(1-\beta)}.$$
--   The endpoints $\alpha\in\{0,1\}$ are included, with the convention $0\log 0=0$.
--
--   This is the χ²-type upper bound on Bernoulli relative entropy. With the entropy bound on binomial coefficients it gives the point-probability lower bound (5) for binomial random variables used in the proof of Claim 5.6.
--
--   Differences from the source:
--   - encoding: KL divergence between Bernoulli distributions, base 2 → klBits of the measures a·δ_true + (1−a)·δ_false on Bool; reason: Mathlib's klDiv on these two-point measures, divided by ln 2, is α log₂(α/β) + (1−α) log₂((1−α)/(1−β)) with 0 log 0 = 0
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Fact 3.18, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_KL

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Fact 3.18, PDF p.15 (printed p.13). For `α ∈ [0,1]` and `β ∈ (0,1)`, the base-2 KL
divergence between the Bernoulli laws satisfies `d_KL(α‖β) ≤ log₂(e) (α−β)² / (β(1−β))`. -/
theorem fact_3_18 (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    klBits (bernoulliLaw a) (bernoulliLaw b) ≤
      ENNReal.ofReal (Real.logb 2 (Real.exp 1) * (a - b) ^ 2 / (b * (1 - b))) := by sorry

end ParallelMatroidBasis.Main
