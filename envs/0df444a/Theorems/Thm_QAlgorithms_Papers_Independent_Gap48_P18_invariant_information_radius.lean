-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_invariant_information_radius
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.invariant_information_radius
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:39:53.417358+00:00
-- url     : https://prove2.me/theorems/615e933f-cdec-4e9a-a990-12e215eec850
-- title:
--   Corollary 9
-- statement:
--   Let $A$ be nonempty and let $F_0$ be any subfamily of the CPTP maps carrying $A$ into its closed convex hull and preserving its capacity. Let $\mathrm{Inv}_{F_0}$ be their common fixed states. Then
--
--   $$\bar C(A)=\inf_{\sigma\in\mathrm{Inv}_{F_0}\cap\overline{\operatorname{co}}A}\sup_{\rho\in A}D(\rho\|\sigma).$$
--
--   An empty indexing set gives infinity. If that intersection is the singleton $\{\sigma_0\}$, the capacity is $\sup_{\rho\in A}D(\rho\|\sigma_0)$, and at finite capacity $\Omega(A)=\sigma_0$. This allows symmetry reduction of the information radius.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 35, Corollary 9

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

/-- Corollary 9, arXiv:quant-ph/0510073v2, PDF pp.35.
 -/
theorem invariant_information_radius {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (F : Set (StateChannel I I))
    (hF : F ⊆ PreservingChannels A) :
    setChiCapacity A = (⨅ sigma : {s : State I // CommonChannelInvariant F s ∧ s ∈ stateClosedConvexHull A},
      radius A sigma.val) ∧
    ({s : State I | CommonChannelInvariant F s ∧ s ∈ stateClosedConvexHull A} = ∅ → setChiCapacity A = ⊤) ∧
    (∀ sigma : State I, sigma ∈ stateClosedConvexHull A → CommonChannelInvariant F sigma →
      (∀ tau ∈ stateClosedConvexHull A, CommonChannelInvariant F tau → tau = sigma) →
      setChiCapacity A = radius A sigma ∧
        (setChiCapacity A < ⊤ → optimalAverage A hA = sigma)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
