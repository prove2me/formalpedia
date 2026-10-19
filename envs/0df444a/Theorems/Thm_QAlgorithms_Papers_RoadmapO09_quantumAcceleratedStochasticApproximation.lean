-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO09_quantumAcceleratedStochasticApproximation
-- name    : QAlgorithms.Papers.RoadmapO09.quantumAcceleratedStochasticApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:37:33.895672+00:00
-- url     : https://prove2.me/theorems/9f1b2a19-2950-4d6e-9024-fe85572b69ff
-- title:
--   Quantum accelerated stochastic approximation: expected accuracy and query complexity
-- statement:
--   Let $d\ge 1$ and let $f:\mathbb R^d\to\mathbb R$ be differentiable and globally convex. Suppose $f$ attains its global minimum at a point $x_\star$ with $\|x_\star\|_2\le R$, where $L,R\ge0$ are public bounds. For every query point $x$, the stochastic gradient is drawn from a measurable probability law satisfying
--
--   $$
--   \mathbb E[g(x)]=\nabla f(x),\qquad \mathbb E\|g(x)\|_2^2\le L^2.
--   $$
--
--   Assume coherent unitary access to this gradient law, preserving the query point and allowing arbitrary garbage, and access to the inverse oracle. The implementation uses normalized zero registers, Born measurement laws, and known Gaussian preparation and reordering operations that construct the smoothed oracle with one gradient-oracle call. These operations and the mean-estimation routine are fixed before the unknown objective and oracle. The mean-estimation interface cited on p.8 is realized, rather than assumed as a convergence hypothesis: for any sampling oracle with variance at most $L^2$, requested error $0<\eta\le L$, and $0<\delta<1$, its execution has total probability one and finite expected calls, and its estimate is within Euclidean distance $\eta$ of the mean with probability at least $1-\delta$.
--
--   For any $\epsilon>0$, run Algorithm 3 with fresh Algorithm 2 gradient estimates. In the nontrivial case $L,R>0$ and $\epsilon<LR$, its parameters are
--
--   $$
--   T=\left\lceil4d^{1/4}LR/\epsilon\right\rceil,\quad
--   \widehat\sigma=\frac{d^{1/8}}8\sqrt{\frac{L\epsilon}{R}},\quad
--   r=\frac{\epsilon}{4\sqrt d L},\quad
--   \gamma=\frac{R\sqrt{6L/r}}{(T+2)^{3/2}\widehat\sigma}.
--   $$
--
--   It starts from $x_1=x_1^{\mathrm{ag}}=0$. At iteration $t$, set $\beta_t=(t+1)/2$, $\gamma_t=(t+1)\gamma/2$, and $x_t^{\mathrm{md}}=\beta_t^{-1}x_t+(1-\beta_t^{-1})x_t^{\mathrm{ag}}$. Use Algorithm 2 on the Gaussian-smoothed gradient law at $x_t^{\mathrm{md}}$, then use the printed ball-constrained update
--
--   $$
--   x_{t+1}=\operatorname*{arg\,min}_{\|z\|_2\le R}
--   \left\{\gamma_t\langle\widetilde g_t,z-x_t^{\mathrm{md}}\rangle+
--   \frac L{2r}\|x_t^{\mathrm{md}}-z\|_2^2\right\},\qquad
--   x_{t+1}^{\mathrm{ag}}=\beta_t^{-1}x_{t+1}+(1-\beta_t^{-1})x_t^{\mathrm{ag}}.
--   $$
--
--   The returned point is $x_{\mathrm{out}}=x_{T+1}^{\mathrm{ag}}$. The same execution, including its classical randomness and quantum measurements, has total probability one and satisfies
--
--   $$
--   \mathbb E[f(x_{\mathrm{out}})-f(x_\star)]\le\epsilon,\qquad
--   \mathbb E[Q]=\widetilde O\!\left(d^{5/8}(LR/\epsilon)^{3/2}\right).
--   $$
--
--   Here $Q$ counts every call to the original gradient oracle and its inverse. Its expectation is finite; the positive geometric level in Algorithm 2 allows an unbounded query count. Explicitly, there are absolute constants $C>0$, an integer $p\ge0$, and a threshold $a\ge1$, all independent of the dimension, bounds, accuracy, objective, probability laws, and register realization, such that whenever $LR/\epsilon\ge a$,
--
--   $$
--   \mathbb E[Q]\le C d^{5/8}(LR/\epsilon)^{3/2}
--   \max\{1,\log(2+d)+|\log\epsilon|+|\log L|+|\log R|\}^{p}.
--   $$
--
--   If $L=0$, $R=0$, or $\epsilon\ge LR$, the implementation returns $0$ with no queries and retains the expected-accuracy guarantee. The minimizing point $x_\star$ is used only to express the guarantee and is not supplied to the algorithm. This result gives the expected-query speedup of the paper's quantum accelerated stochastic approximation method; it asserts no gate-complexity or fixed-confidence output bound.
--
--   **Formalization Note** The real iteration budget on p.13 is rounded upward to define a finite loop. The statement preserves the proximal center and all other displayed constants. The p.13/p.15 pointwise gradient assertion is incompatible with the stated second-moment hypothesis; the proof also contains an extra factor $1/r$, a reversed optimum-gap sign, and a constant gap in its use of Lemma 5. These are disclosed proof gaps, not additional hypotheses or silent changes to Algorithm 3. No directional-mean definition is imported or reconstructed.
-- source:
--   Quantum speedups for stochastic optimization, arXiv:2308.01582v2, Theorem 5 (Formal version of Theorem 1, Part 1), PDF p. 13. https://arxiv.org/abs/2308.01582v2 . PDF SHA-256: 6ef6b5cba1d0983003e6e78b5a5028c5fc32b4e3c1f716c81b23fb523cb24c7a.

import Definitions.Def_QAlgorithms_Defs_StochasticAcceleration
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO09

open QAlgorithms.StochasticOptimization

/-- Sidford–Zhang, arXiv:2308.01582v2, Theorem 5 (PDF p.13), with Problem 1
(p.5) and Definitions 1–3 (pp.3–4): the constructed Algorithm 3 has expected
objective error at most `eps` and expected query complexity
`Otilde(d^(5/8) * (L*R/eps)^(3/2))` for the same execution.

The existential routine implements the cited mean-estimator interface of Lemma 1
(p.8); its accuracy is a conclusion, not an assumed variance-reduction theorem.
Algorithms 1 and 2 are the frozen `quantumMeanEstimationPlus` and
`quantumVarianceReduction`, including independent fresh samples and the unbounded
positive geometric level. Gaussian preparation and register reordering are known
operations, chosen before the objective and oracle. Every expanded smoothed query
counts one call to the original gradient oracle or its inverse.

The finite loop uses the ceiling of the printed real iteration budget. All other
parameters and the proximal quadratic centered at `xmd` are preserved. No
pointwise gradient bound, smoothness hypothesis or retuned precision is imposed.
The p.13/p.15 pointwise-bound assertion does not follow from Definition 2; Eq.(12)
has an extra `1/r`, and its subsequent gap identity has the wrong sign. Moreover,
the displayed Lemma 5 bound does not imply the claimed accuracy with the printed
constants. These are recorded proof gaps; this declaration retains the original
Theorem 5 target rather than assuming those intermediate claims.
-/
theorem quantumAcceleratedStochasticApproximation :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ (d : ℕ), 1 ≤ d →
    ∀ (H W : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W],
    ∀ (registers : GradientRegisters d H W) (sampling : SamplingRegisters d H)
      (layouts : (r : ℝ) → (hr : 0 < r) → GaussianQueryLayout d H W registers r hr),
    (∀ r hr, (layouts r hr).outputRegisters = sampling) →
    ∃ M : QuantumMeanEstimationProgram d H,
      (∀ L eta delta : ℝ, 0 < L → 0 < eta → eta ≤ L → 0 < delta → delta < 1 →
        ∀ O : QuantumSamplingOracle d H sampling,
        Integrable (fun v => v) O.distribution →
        Integrable (fun v => ‖v - ∫ w, w ∂O.distribution‖ ^ 2) O.distribution →
        (∫ v, ‖v - ∫ w, w ∂O.distribution‖ ^ 2 ∂O.distribution) ≤ L ^ 2 →
        ∃ hmean : IsMeasurableProgram O (M.program L eta delta),
          let meanLaw := executionLaw (M.program L eta delta) O hmean
          meanLaw Set.univ = 1 ∧ expectedCalls meanLaw < ⊤ ∧
          meanLaw {vq | ‖vq.1 - ∫ v, v ∂O.distribution‖ ≤ eta} ≥
            ENNReal.ofReal (1 - delta)) ∧
      ∀ L R eps : ℝ, 0 ≤ L → 0 ≤ R → 0 < eps →
      ∀ f : Vector d → ℝ, ConvexOn ℝ Set.univ f →
      ∀ O : QuantumStochasticGradientOracle d f H W registers,
      O.stochastic.IsBounded L →
      ∀ xstar : Vector d, ‖xstar‖ ≤ R → (∀ x, f xstar ≤ f x) →
      ∃ hrun : IsMeasurableProgram (samplingOracleOfUnitary sampling O.unitary)
        (acceleratedProgram M layouts L R eps),
        let law := gradientExecutionLaw (acceleratedProgram M layouts L R eps) sampling O hrun
        ExpectedOptimizationContract law f xstar eps ∧
        expectedCalls law < ⊤ ∧
        (threshold ≤ L * R / eps →
          expectedCalls law ≤ ENNReal.ofReal
            (C * (d : ℝ) ^ (5 / 8 : ℝ) * (L * R / eps) ^ (3 / 2 : ℝ) *
              max 1 (Real.log (2 + d) + |Real.log eps| + |Real.log L| + |Real.log R|) ^ p)) ∧
        ((L = 0 ∨ R = 0 ∨ L * R ≤ eps) → expectedCalls law = 0) := by sorry

end QAlgorithms.Papers.RoadmapO09
