-- Prove2me | Theorems.Thm_UnderstandingML_pac_bayes_moment_bound
-- name    : UnderstandingML.pac_bayes_moment_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T06:07:35.392536+00:00
-- url     : https://prove2.me/theorems/18816119-1192-4700-af51-0e0d3263cd51
-- title:
--   Proof of Theorem 31.1: for every h, E_S[e^{2(m−1)(L_D(h) − L_S(h))²}] ≤ m for a [0,1]-valued loss
-- statement:
--   **Proof of Theorem 31.1 (p. 417).** Next, we claim that for all $h$ we have $\mathbb{E}_S[e^{2(m-1)\Delta(h)^2}] \le m$, where $\Delta(h) = L_D(h) - L_S(h)$; the book derives this from Hoeffding's inequality $P_S[\Delta(h) \ge \epsilon] \le e^{-2m\epsilon^2}$ via Exercise 1.
--
--   Formally: for a $[0,1]$-valued measurable loss and $S \sim D^m$, $m \ge 1$. (The one-sided tail hypothesis of Exercise 1 does not by itself imply the claim; the bound follows for instance from Hoeffding's lemma and the Gaussian representation of $e^{a\Delta^2}$, which gives $\sqrt m$.)
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §31.1 p. 417, the claim E_S[e^{2(m−1)Δ(h)²}] ≤ m in the proof of Theorem 31.1 (and Exercise 1, p. 417)

import Definitions.Def_UnderstandingML_PACBayes

open MeasureTheory

namespace UnderstandingML

/-- **Proof of Theorem 31.1** (p. 417): for every `h`, `E_S[e^{2(m−1)Δ(h)²}] ≤ m`, where
`Δ(h) = L_D(h) − L_S(h)` for a `[0, 1]`-valued loss and `S ∼ D^m`. (The book derives this from
Hoeffding's tail bound via Exercise 1; the tail hypothesis of that exercise, being one-sided,
is not sufficient, but the bound holds, e.g. from Hoeffding's lemma and the Gaussian
representation of `e^{aΔ²}`, which even gives `√m`.) `m ≥ 1`, `ℓ(h, ·)` measurable. -/
theorem pac_bayes_moment_bound {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (h : Hyp) (hmeas : Measurable (loss h)) (hloss : ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1)
    (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m) :
    ∫ S, Real.exp (2 * (m - 1) * (risk loss D h - empRisk loss S h) ^ 2) ∂(iidLaw D m) ≤ m := by sorry

end UnderstandingML
