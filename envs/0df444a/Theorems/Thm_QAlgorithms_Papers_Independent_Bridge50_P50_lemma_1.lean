-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_1
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:23:29.65996+00:00
-- url     : https://prove2.me/theorems/70aee536-ac6f-4f2a-86d1-7f4cfb5074a5
-- title:
--   Lemma 1: Normalized testing-divergence properties
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. For $0<\varepsilon<1$, let $P,Q$ be probability measures on discrete subsets $S,T\subseteq\mathcal S$, with barycenters $\rho,\sigma$. Define $D_h^\varepsilon(\rho\|\sigma)=-\log_2[\beta_{1-\varepsilon}(\rho\|\sigma)/(1-\varepsilon)]$, where $\beta$ minimizes $\operatorname{tr}(A\sigma)$ over effects $0\le A\le I$ satisfying $\operatorname{tr}(A\rho)\ge1-\varepsilon$. Then
--   $$
--   D_h^\varepsilon(\rho\|\sigma)\ge0,\quad D_h^\varepsilon(\rho\|\sigma)=0\iff\rho=\sigma,
--   $$
--   $$
--   D_h^\varepsilon(\mathcal M(\rho)\|\mathcal M(\sigma))\le D_h^\varepsilon(\rho\|\sigma)
--   \le\inf_{\omega\in T}\left(D_h^\varepsilon(\rho\|\omega)+\log_2\frac1{Q(\omega)}\right),
--   \qquad D_h^\varepsilon(\rho\|\sigma)\le\sup_{\tau\in S}D_h^\varepsilon(\tau\|\sigma).
--   $$
--   The first comparison holds for every finite-dimensional CPTP map $\mathcal M$. A zero $Q$ atom contributes $+\infty$; the extended infimum and supremum express the source's minimum and maximum without requiring attainment on infinite discrete sets.
--
--   These properties support one-shot bounds by manipulating physical comparison states.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 5, Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Lemma 1, PDF pp.5–6: all four properties of the normalized testing divergence.
Discrete sets may be infinite; zero Q atoms contribute infinity in the infimum. -/
theorem lemma_1 {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [DecidableEq J] [Nonempty J]
    (e : ℝ) (he : 0 < e ∧ e < 1) (S T : Set (Mat I))
    [DiscreteTopology S] [DiscreteTopology T]
    (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho)
    (hT : ∀ sigma ∈ T, QAlgorithms.IsDensityMatrix sigma)
    (P Q : ProbabilityMeasure (Mat I)) (hP : P ∈ measuresOn S) (hQ : Q ∈ measuresOn T) :
    (0 ≤ normalizedTestingDivergence e (stateBarycenter P) (stateBarycenter Q) ∧
      (normalizedTestingDivergence e (stateBarycenter P) (stateBarycenter Q) = 0 ↔ stateBarycenter P = stateBarycenter Q)) ∧
    (∀ M : QAlgorithms.Superop I J, QAlgorithms.IsChannel M →
      normalizedTestingDivergence e (M (stateBarycenter P)) (M (stateBarycenter Q)) ≤
        normalizedTestingDivergence e (stateBarycenter P) (stateBarycenter Q)) ∧
    (normalizedTestingDivergence e (stateBarycenter P) (stateBarycenter Q) ≤
      ⨅ omega : T, normalizedTestingDivergence e (stateBarycenter P) omega.val +
        (if (Q : Measure (Mat I)) {omega.val} = 0 then ⊤ else
          ENNReal.ofReal (logTwo (1 / ((Q : Measure (Mat I)) {omega.val}).toReal)))) ∧
    (normalizedTestingDivergence e (stateBarycenter P) (stateBarycenter Q) ≤
      ⨆ tau : S, normalizedTestingDivergence e tau.val (stateBarycenter Q)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
