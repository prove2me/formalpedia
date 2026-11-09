-- Prove2me | Theorems.Thm_WangRenyiEntropy_Noninteger_coordinate_bias_variance
-- name    : WangRenyiEntropy.Noninteger.coordinate_bias_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:36.161226+00:00
-- url     : https://prove2.me/theorems/02c82169-76bb-4c5b-8216-6b2c5dae0805
-- title:
--   Lemma 4.2 — bias and variance of the coordinate estimate
-- statement:
--   Fix positive noninteger $\alpha$, a uniform approximation constant $c_\alpha$ from Lemma 2.2, any $d\ge1$, and any best degree-$K$ approximant $Q_K$. Put $L=\log(ed)$, $J=\lceil4\alpha\rceil+3$ and $C_\alpha=c_\alpha(256J)^{32J}$. For $n>0$, $p\ge0$ and independent $X,Y\sim\operatorname{Poi}(np)$, let $Z$ be the exact coordinate estimator (20)–(22). It has finite first and second moments and
--   $$|\mathbb EZ-p^\alpha|\le C_\alpha(nL)^{-\alpha},$$
--   $$\operatorname{Var}Z\le C_\alpha^2\left(\frac{L^{2\alpha}d^{1/4}}{n^{2\alpha}}+\mathbf1_{\alpha>1/2}\frac{p^{2\alpha-1}}n\right).$$
--   The indicator is a branch: its potentially nonpositive power of $p$ is absent at $\alpha\le1/2$. This statement retains zero rate and uses actual Poisson expectations, with no bias or variance bound assumed.
--
--   Differences from the source:
--   - encoding: cα from Lemma 2.2 and Cα = cα(256J)^(32J) → any single c ≥ 1 satisfying both uniform bounds for every degree and every best approximant; C is computed from that c; reason: Lemma 2.2 asserts existence of this c; no error bound or success property is placed in the estimator definition
--   - encoding: finite expectations and variance of the displayed estimator → integrability and square integrability are explicit conclusions alongside the inequalities; reason: Poisson laws have all required moments and the large-count branch avoids negative powers at zero; these are conclusions, never extra hypotheses
--   - generalization: p is a probability coordinate, hence 0 ≤ p ≤ 1 → every scalar p ≥ 0; reason: the proof depends only on λ = np and remains valid for all nonnegative λ; every source coordinate is included
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 13 / PDF 15, Lemma 4.2, Eqs. (23)–(24)

import Mathlib
import Definitions.Def_WangRenyiEntropy_Noninteger_Estimator

open MeasureTheory

namespace WangRenyiEntropy.Noninteger

/-- Lemma 4.2, printed p.13 / PDF p.15. The scalar p is nonnegative,
including zero; n is a positive Poisson mean, not necessarily integral. -/
theorem coordinate_bias_variance (α c : ℝ) (hα : NonintegerOrder α)
    (hc : ApproximationConstant α c) (d : ℕ) (hd : 1 ≤ d)
    (Q : Polynomial ℝ) (hQ : IsBestApproximation α (approximationDegree d) Q)
    (n p : ℝ) (hn : 0 < n) (hp : 0 ≤ p) :
    let μ := coordinateLaw n p
    let Z := coordinateEstimate α n d Q
    Integrable Z μ ∧ Integrable (fun xy => Z xy ^ 2) μ ∧
    |(∫ xy, Z xy ∂μ) - Real.rpow p α| ≤ estimatorConstant α c * Real.rpow (n * logScale d) (-α) ∧
    estimatorVariance μ Z ≤ (estimatorConstant α c) ^ 2 *
      (Real.rpow (logScale d) (2 * α) * Real.rpow d (1 / 4) / Real.rpow n (2 * α) +
        if 1 / 2 < α then Real.rpow p (2 * α - 1) / n else 0) := by sorry

end WangRenyiEntropy.Noninteger
