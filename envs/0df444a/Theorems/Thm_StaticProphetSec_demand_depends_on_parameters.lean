-- Prove2me | Theorems.Thm_StaticProphetSec_demand_depends_on_parameters
-- name    : StaticProphetSec.demand_depends_on_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:22.749018+00:00
-- url     : https://prove2.me/theorems/c3e79764-6c27-4011-84c3-8635edec86c6
-- title:
--   p.17 — $\mathbb E[\mathrm{UT}_k(D)]$ and $\mathbb E[\mathrm{AR}_k(D)]$ depend on $F$ only through the parameters
-- statement:
--   Under the policy $(t,p)$, demand $D$ has the law of a sum $D_q$ of independent Bernoulli variables with means $q_i=\mathbb P(V_i>t)+p\,\mathbb P(V_i=t)$. In particular
--
--   $$\mathbb E[\mathrm{UT}_k(D)]=\mathbb E[\mathrm{UT}_k(D_q)],\qquad\mathbb E[\mathrm{AR}_k(D)]=\mathbb E[\mathrm{AR}_k(D_q)].$$
--
--   So both terms of the lower bound in Lemma 1 depend on $F$ only through the parameters $q_i$, and the rest of the proof is about sums of Bernoulli variables.
--
--   Differences from the source:
--
--   - generalization: parameters $p_i=1-F_i(t)$ → parameters $q_i=\mathbb P(V_i>t)+p\,\mathbb P(V_i=t)$ of the policy $(t,p)$; reason: Remark 1, p.5; $p=0$ recovers the source
--   - encoding: the terms depend on $F$ only through the parameters → each term equals an explicit function of the parameters; reason: this is the precise form of the sentence and implies it
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, p.17

import Mathlib
import Definitions.Def_StaticProphetSec_UT
import Definitions.Def_StaticProphetSec_AR
import Definitions.Def_StaticProphetSec_expUtil
import Definitions.Def_StaticProphetSec_expAR
import Definitions.Def_StaticProphetSec_tieParam
import Definitions.Def_StaticProphetSec_pbE

open MeasureTheory

namespace StaticProphetSec

/-- Reduction to the parameters (Arnosti & Ma, arXiv:2108.12893v2, p.17: "both terms in the lower
bound in Lemma 1 depend on F only through the parameters p_i = 1 - F_i(t)"), for the policy
`(t, p)`: demand has the Poisson binomial law with means
`q_i = P(V_i > t) + p · P(V_i = t)`, so `E[UT_k(D)]` and `E[AR_k(D)]` are `E[UT_k(D_q)]` and
`E[AR_k(D_q)]`. -/
theorem demand_depends_on_parameters {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, μ i (Set.Iio 0) = 0)
    (t p : ℝ) (ht : 0 ≤ t) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    expUtil k μ t p = ENNReal.ofReal (pbE (UT k) (tieParam μ t p)) ∧
    expAR k μ t p = ENNReal.ofReal (pbE (AR k) (tieParam μ t p)) := by sorry

end StaticProphetSec
