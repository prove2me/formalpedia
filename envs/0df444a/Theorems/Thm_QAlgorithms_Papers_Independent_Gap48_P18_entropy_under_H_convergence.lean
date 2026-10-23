-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_entropy_under_H_convergence
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.entropy_under_H_convergence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:54:19.267332+00:00
-- url     : https://prove2.me/theorems/8b58df1a-d44f-4f8c-b195-0e09cadcdce2
-- title:
--   Proposition 2
-- statement:
--   Let $\sigma$ have finite entropy, and let $\operatorname{dc}(\sigma)=\inf\{t>0:\operatorname{Tr}\sigma^t<\infty\}$. If $\operatorname{dc}(\sigma)<1$, every sequence H-converging to $\sigma$ satisfies
--
--   $$D(\rho_n\|\sigma)\to0\quad\Longrightarrow\quad H(\rho_n)\to H(\sigma).$$
--
--   If $\operatorname{dc}(\sigma)=1$, every $h\in[H(\sigma),\infty]$ is the entropy limit of some finite-rank sequence H-converging to $\sigma$. This characterizes the spectral obstruction to entropy continuity under H-convergence.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 13, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 2, arXiv:quant-ph/0510073v2, PDF pp.13.
Finite support means finite operator rank, not finite coordinate support. Infinite target entropy is retained. -/
theorem entropy_under_H_convergence {I : Type} [Countable I] [Nonempty I]
    (sigma : State I) (hfinite : stateEntropyNats sigma < ⊤) :
    (decreaseCoefficient sigma < 1 → ∀ seq : ℕ → State I,
      HConverges seq sigma → Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 (stateEntropyNats sigma))) ∧
      (decreaseCoefficient sigma = 1 → ∀ h : ℝ≥0∞, stateEntropyNats sigma ≤ h →
        ∃ seq : ℕ → State I, (∀ n, PositiveFiniteRankState (seq n)) ∧ HConverges seq sigma ∧
          Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 h)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
