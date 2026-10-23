-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_entropy_maximizing_sequences_H_limit_and_attainment
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.entropy_maximizing_sequences_H_limit_and_attainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:56:54.10564+00:00
-- url     : https://prove2.me/theorems/ef70264b-b87e-4ee0-89e5-609ad576a31a
-- title:
--   Lemma 2 footnote2: H-limit and attainment
-- statement:
--   Let $A$ be nonempty, closed, and convex with finite entropy supremum $S$. All maximizing sequences have the same limit $\rho_*(A)\in A$, and in fact
--
--   $$H(\rho_n)\to S\quad\Longrightarrow\quad D(\rho_n\|\rho_*(A))\to0.$$
--
--   If $\operatorname{Tr}\rho_*(A)^t<\infty$ for some $0<t<1$, then $H(\rho_*(A))=S$: the common limit is the Gibbs maximizer. This is the explicit strengthening stated in Lemma 2's footnote.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 7, Lemma 2 footnote2: H-limit and attainment

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

/-- Lemma 2 footnote2: H-limit and attainment, arXiv:quant-ph/0510073v2, PDF pp.7.
 -/
theorem entropy_maximizing_sequences_H_limit_and_attainment {I : Type}
    [Countable I] [Nonempty I] (A : Set (State I)) (hA : A.Nonempty)
    (hclosed : IsClosed A) (hconvex : CoefficientConvexStates A) (hfinite : entropySup A < ⊤) :
    ∃! omega : State I, omega ∈ A ∧
      (∀ seq : ℕ → State I, (∀ n, seq n ∈ A) →
        Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 (entropySup A)) →
          Tendsto seq atTop (𝓝 omega) ∧ HConverges seq omega) ∧
      ((∃ t : ℝ, 0 < t ∧ t < 1 ∧ spectralPowerTrace omega t < ⊤) →
        stateEntropyNats omega = entropySup A) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
