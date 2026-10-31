-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_pressure_variational_principle
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.pressure_variational_principle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:14:27.32086+00:00
-- url     : https://prove2.me/theorems/46dcb8ca-3b5c-4e65-8f67-6431151f0124
-- title:
--   Proposition 2.6: all six pressure and variational-principle clauses
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   For finite $(\epsilon,n)$-spanning and separated sets $E$, let $S(\mathcal G,\epsilon,n)$ and $N(\mathcal G,\epsilon,n)$ be the infimum and supremum, respectively, of $\sum_{x\in E}e^{G_n(x)}$. Write $p^0(g)=p((S_ng))$ and $\|\mathcal G\|_* =\limsup_n\|G_n\|_\infty/n$. All six assertions hold:
--
--   1. The small-radius limits of both upper and lower exponential growth rates of $S$ and $N$ coincide with $p(\mathcal G)$. Pressure is convex, never $-\infty$, and is either identically $+\infty$ or everywhere real on $\mathcal A(M)$.
--   2. For any continuous approximating family $g_k$, $p^0(g_k)\to p(\mathcal G)$.
--   3. $h_{\rm top}(\varphi)=p^0(0)=\sup_{Q\in\mathcal P_\varphi}h_\varphi(Q)=\sup_{Q\in\mathcal E_\varphi}h_\varphi(Q)$; every AA pressure is finite exactly when topological entropy is finite.
--   4. If topological entropy is finite, $|p(\mathcal G)-p(\mathcal H)|\le\|\mathcal G-\mathcal H\|_*$ for all AA sequences.
--   5. The variational identity is
--   $$p(\mathcal G)=\sup_{Q\in\mathcal P_\varphi(M)}\{\mathcal G(Q)+h_\varphi(Q)\}.$$
--   6. If invariant entropy is upper semicontinuous, then for every invariant $P$ and every fixed AA base $\mathcal G$,
--   $$h_\varphi(P)=\inf_{\mathcal H\in\mathcal A(M)}[p(\mathcal H)-\mathcal H(P)]=\inf_{v\in C(M)}[p(\mathcal G+Sv)-(\mathcal G+Sv)(P)].$$
--   Here $\mathcal G+Sv=(G_n+S_nv)$. The extended formulas retain infinite entropy; no global finiteness assumption is added.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 22, Proposition 2.6: all six pressure and variational-principle clauses

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Proposition 2.6, arXiv:1712.05167v3, PDF pp.22--23: all six clauses.
Only clause (4) assumes finite entropy; all supremum/infimum identities use
EReal and preserve +infinity. In (2.17) the entire perturbed sequence is evaluated. -/
theorem pressure_variational_principle (phi : M → M) (hphi : Continuous phi) :
    ((∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G →
      separatedSetPressure phi G ≠ ⊥ ∧
      Tendsto (partitionGrowthUpper (spanningSum phi G)) (𝓝[>] (0 : ℝ)) (𝓝 (separatedSetPressure phi G)) ∧
      Tendsto (partitionGrowthLower (spanningSum phi G)) (𝓝[>] (0 : ℝ)) (𝓝 (separatedSetPressure phi G)) ∧
      Tendsto (partitionGrowthUpper (separatedSum phi G)) (𝓝[>] (0 : ℝ)) (𝓝 (separatedSetPressure phi G)) ∧
      Tendsto (partitionGrowthLower (separatedSum phi G)) (𝓝[>] (0 : ℝ)) (𝓝 (separatedSetPressure phi G))) ∧
      (∀ G H : ℕ → M → ℝ, AsymptoticallyAdditive phi G → AsymptoticallyAdditive phi H →
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
          separatedSetPressure phi (fun n x => a * G n x + b * H n x) ≤
            (a : EReal) * separatedSetPressure phi G + (b : EReal) * separatedSetPressure phi H) ∧
      ((∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G → separatedSetPressure phi G = ⊤) ∨
        (∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G → FinitePressure phi G))) ∧
    (∀ G F : ℕ → M → ℝ, AsymptoticallyAdditive phi G → ApproximatingFamily phi G F →
      Tendsto (fun k : ℕ => additivePressure phi (F (k + 1))) atTop (𝓝 (separatedSetPressure phi G))) ∧
    (topologicalEntropy phi = additivePressure phi (fun _ => 0) ∧
      additivePressure phi (fun _ => 0) =
        ⨆ (Q : ProbabilityMeasure M) (_ : ProbabilityInvariant phi Q), metricEntropy phi Q) ∧
    (topologicalEntropy phi =
      ⨆ (Q : ProbabilityMeasure M) (_ : Ergodic phi (Q : Measure M)), metricEntropy phi Q) ∧
    ((∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G → FinitePressure phi G) ↔
      topologicalEntropy phi < ⊤) ∧
    (topologicalEntropy phi < ⊤ → ∀ G H : ℕ → M → ℝ,
      AsymptoticallyAdditive phi G → AsymptoticallyAdditive phi H →
      ((|((separatedSetPressure phi G).toReal) - ((separatedSetPressure phi H).toReal)| : ℝ) : EReal) ≤
        potentialSeminorm (fun n x => G n x - H n x)) ∧
    (∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G →
      separatedSetPressure phi G = ⨆ (P : ProbabilityMeasure M) (_ : ProbabilityInvariant phi P),
        (potentialEvaluation G P : EReal) + metricEntropy phi P) ∧
    (EntropyUSC phi → ∀ P : ProbabilityMeasure M, ProbabilityInvariant phi P →
      metricEntropy phi P = ⨅ (G : ℕ → M → ℝ) (_ : AsymptoticallyAdditive phi G),
        separatedSetPressure phi G - (potentialEvaluation G P : EReal)) ∧
    (EntropyUSC phi → ∀ G : ℕ → M → ℝ, AsymptoticallyAdditive phi G →
      ∀ P : ProbabilityMeasure M, ProbabilityInvariant phi P →
        metricEntropy phi P = ⨅ V : C(M, ℝ),
          separatedSetPressure phi (fun n x => G n x + orbitSum phi V n x) -
            (potentialEvaluation (fun n x => G n x + orbitSum phi V n x) P : EReal)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
