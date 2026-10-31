-- Prove2me | Theorems.Thm_UnbiasedTimeAvg_eq_H_3
-- name    : UnbiasedTimeAvg.eq_H_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:51.180209+00:00
-- url     : https://prove2.me/theorems/25aaca7b-8ed7-46a1-ad06-376b6711c3a4
-- title:
--   (H.3) — $\mathrm{Var}(V_1+q^{-1}QV_2)\le\mathrm{Var}(V_1)+q^{-1}\mathbb E(V_2^2)$
-- statement:
--   Let $V_1,V_2$ be independent square-integrable random variables, $q\in(0,1]$, and $Q$ a binary ($\{0,1\}$-valued) random variable independent of $(V_1,V_2)$ with $\Pr(Q=1)=q$. Set $V=V_1+q^{-1}QV_2$. Then $V$ is square-integrable and
--   $$\mathrm{Var}(V)=\mathrm{Var}(V_1)+q^{-2}\,\mathrm{Var}(QV_2)\le\mathrm{Var}(V_1)+q^{-1}\,\mathbb E(V_2^2).\qquad(\mathrm H.3)$$
--
--   Applied with $V_1=f_{k,0}$ and $V_2=Z'_k$, it bounds the variance of $\hat f_k$.
--
--   Differences from the source:
--   - generalization: the hypotheses of Proposition H.1, including finite expected running times τ_1, τ_2 → the same hypotheses without τ_1, τ_2; reason: (H.3) does not involve the running times; with them added the statement is the source's
--   - encoding: V square-integrable → `MemLp V 2 P` added to the conclusion; reason: makes Var(V) the true variance; it follows from the hypotheses
--   - encoding: "binary random variable" → `Measurable Q` with `Q ω = 0 ∨ Q ω = 1`; reason: the meaning of a binary random variable
--   - encoding: q ∈ (0, 1] → `0 < q`, with q ≤ 1 not a separate hypothesis; reason: Pr(Q = 1) = q already forces q ≤ 1; same instances
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), Proposition H.1 (hypotheses) and (H.3), p.29

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace UnbiasedTimeAvg

/-- **(H.3): variance of `V_1 + q⁻¹QV_2`.** Kahalé, arXiv:2209.09581v1, Proposition H.1 and
(H.3), p.29: "Let `V_1` and `V_2` be independent square integrable random variables … Let `Q` be a
binary random variable independent of `(V_1, V_2)`, with `Pr(Q = 1) = q`, where `q ∈ (0, 1]`. Set
`V = V_1 + q⁻¹QV_2`. … `Var(V) = Var(V_1) + q⁻²Var(QV_2) ≤ Var(V_1) + q⁻¹E(V_2²)` (H.3)."

Only the variance identity and bound are stated; the running-time part of Proposition H.1 is not
used by the goal. The first conjunct (`V` is square-integrable) makes the variances true ones.

**Formalization Note.** "Binary random variable" is a measurable `Q` with values in `{0, 1}`. The
bound `q ≤ 1` is not a separate hypothesis: it follows from `Pr(Q = 1) = q`. -/
theorem eq_H_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (V₁ V₂ Q : Ω → ℝ) (q : ℝ) (hq : 0 < q)
    (hV₁ : MemLp V₁ 2 P) (hV₂ : MemLp V₂ 2 P) (hV_indep : IndepFun V₁ V₂ P)
    (hQ_meas : Measurable Q) (hQ_bin : ∀ ω, Q ω = 0 ∨ Q ω = 1)
    (hQ_law : P {ω | Q ω = 1} = ENNReal.ofReal q)
    (hQ_indep : IndepFun Q (fun ω => (V₁ ω, V₂ ω)) P) :
    MemLp (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) 2 P ∧
    variance (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) P
      = variance V₁ P + q⁻¹ ^ 2 * variance (fun ω => Q ω * V₂ ω) P ∧
    variance (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) P
      ≤ variance V₁ P + q⁻¹ * ∫ ω, V₂ ω ^ 2 ∂P := by sorry

end UnbiasedTimeAvg
