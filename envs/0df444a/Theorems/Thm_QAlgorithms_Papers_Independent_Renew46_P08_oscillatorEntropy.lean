-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_oscillatorEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.oscillatorEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:51:48.134797+00:00
-- url     : https://prove2.me/theorems/f1e87e1e-612d-41cb-ad90-2eba152e9da3
-- title:
--   Unnumbered oscillator entropy formula and envelope (42)–(43)
-- statement:
--   Fix $\ell\ge1$, $\hbar>0$ and positive frequencies $\omega_i$. On the full $\ell$-mode Fock space let $H=\sum_i\hbar\omega_i(N_i+1/2)$, $E_0=\frac12\sum_i\hbar\omega_i$ and $E_*=(\prod_i\hbar\omega_i)^{1/\ell}$. The actual entropy supremum $F_H(E)$ over all normalized states of energy at most $E\ge E_0$ is finite and satisfies the attained maximization formula
--
--   $$F_H(E)=\max_{\sum_iE_i=E,\ E_i\ge\hbar\omega_i/2}\ \sum_i g(E_i/(\hbar\omega_i)-1/2)\le\widehat F_{\ell,\omega}(E):=\ell\log\frac{E+E_0}{\ell E_*}+\ell.$$
--
--   The absolute gap $\widehat F_{\ell,\omega}(E)-F_H(E)$ tends to zero as $E\to\infty$. This identifies the exact allocation maximum and its asymptotically exact closed-form envelope, including zero-point energy.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 16, Unnumbered oscillator entropy formula and envelope (42)–(43)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- PDF pp.15–17, (42)–(43): oscillator entropy is an ATTAINED maximum over
coefficientEnergy allocations, the closed-form envelope is an upper bound, and its
absolute gap tends to zero. The full Fock space includes the vacuum. -/
theorem oscillatorEntropy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ell : ℕ} (hell : 0 < ell)
    (b : HilbertBasis (Fin ell → ℕ) ℂ H) (hbar : ℝ) (hhbar : 0 < hbar)
    (omega : Fin ell → ℝ) (homega : ∀ i, 0 < omega i) :
    (∀ E : ℝ, oscillatorGround hbar omega ≤ E →
      oscillatorEntropyBounded b hbar omega E < ⊤ ∧
      (∃ a : Fin ell → ℝ, (∑ i, a i) = E ∧ (∀ i, hbar * omega i / 2 ≤ a i) ∧
        (oscillatorEntropyBounded b hbar omega E).toReal =
          ∑ i, g (a i / (hbar * omega i) - 1/2) ∧
        ∀ c : Fin ell → ℝ, (∑ i, c i) = E → (∀ i, hbar * omega i / 2 ≤ c i) →
          (∑ i, g (c i / (hbar * omega i) - 1/2)) ≤
            (oscillatorEntropyBounded b hbar omega E).toReal) ∧
      (oscillatorEntropyBounded b hbar omega E).toReal ≤ oscillatorEnvelope hbar omega E) ∧
    Tendsto (fun E : ℝ => oscillatorEnvelope hbar omega E -
      (oscillatorEntropyBounded b hbar omega E).toReal) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
