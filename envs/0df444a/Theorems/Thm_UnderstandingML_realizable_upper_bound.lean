-- Prove2me | Theorems.Thm_UnderstandingML_realizable_upper_bound
-- name    : UnderstandingML.realizable_upper_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:56:17.703159+00:00
-- url     : https://prove2.me/theorems/2ea583cc-b80f-4ec4-ab3c-e1014ecab5b9
-- title:
--   §28.3 (realizable upper bound): for m ≥ (8/ε)(2d log(16e/ε) + log(2/δ)), δ < 1/4, an ERM learner has true error ≤ ε w.p. ≥ 1−δ under every realizable (D, f), so m_H(ε,δ) ≤ C(d ln(1/ε) + ln(1/δ))/ε
-- statement:
--   **§28.3.** Here we prove that there exists $C$ such that $H$ is PAC learnable with sample complexity $m_H(\epsilon, \delta) \le C\frac{d\ln(1/\epsilon) + \ln(1/\delta)}{\epsilon}$. We do so by showing that for $m \ge C\frac{d\ln(1/\epsilon) + \ln(1/\delta)}{\epsilon}$, $H$ is learnable using the ERM rule, based on the notion of $\epsilon$-nets.
--
--   Formally: for $\epsilon \in (0,1)$, $\delta \in (0, 1/4)$ and $m \ge \frac8\epsilon(2d\log(16e/\epsilon) + \log(2/\delta))$, every ERM learner has true error at most $\epsilon$ with probability at least $1 - \delta$ under every realizable $(D, f)$ (Theorem 28.3 applied to the error sets $\{x : h(x) \ne f(x)\}$, which have the same VC dimension). $H$ consists of measurable hypotheses with the countable-approximation property of Mission IV (Remark 3.1).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.3 p. 398 (from Theorem 28.3 applied to the error sets)

import Definitions.Def_UnderstandingML_FundamentalProof

open MeasureTheory

namespace UnderstandingML

/-- **§28.3, the upper bound for the realizable case** (p. 398): for
`m ≥ (8/ε)(2d log(16e/ε) + log(2/δ))`, `H` is learnable using the ERM rule, so
`m_H(ε, δ) ≤ C (d ln(1/ε) + ln(1/δ))/ε`. Stated for `ε ∈ (0, 1)`, `δ ∈ (0, 1/4)` (the range
of Theorem 28.3), a realizable pair `(D, f)` and an ERM learner: the probability that the ERM
output has true error above `ε` is at most `δ`. -/
theorem realizable_upper_bound {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ) (hd : vcDim H = d)
    (A : Learner (X × Bool) (X → Bool)) (hA : IsERMLearner loss01 H A) (D : Measure X)
    [IsProbabilityMeasure D] (f : X → Bool) (hf : Measurable f) (hreal : Realizable H D f)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1 / 4) (m : ℕ)
    (hm : 8 / ε * (2 * d * Real.log (16 * Real.exp 1 / ε) + Real.log (2 / δ)) ≤ m) :
    iidLaw (labeledLaw D f) m {S | ε < trueError D f (A m S)} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
