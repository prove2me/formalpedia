-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_generalized_Donald_identity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.generalized_Donald_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:01:12.719092+00:00
-- url     : https://prove2.me/theorems/49b3b490-7231-4545-89f6-c81719fd8a58
-- title:
--   Lemma 4: generalized Donald identity
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For every Borel ensemble $\pi$ and state $\sigma$,
--
--   $$\int H(\rho\Vert\sigma)\,\pi(d\rho)=\int H(\rho\Vert\bar\rho(\pi))\,\pi(d\rho)+H(\bar\rho(\pi)\Vert\sigma).$$
--
--   Both sides may be infinite. No finite-entropy or support-inclusion hypothesis is imposed. This is Donald’s identity for generalized ensembles.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 12, Lemma 4: generalized Donald identity

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 4, PDF p.12, (16): generalized Donald identity. Both sides may
be infinite; all addition and integration are nonnegative extended operations. -/
theorem generalized_Donald_identity {I : Type} [Countable I]
    (mu : GeneralizedEnsemble I) (sigma : State I) :
    (∫⁻ rho : State I, extendedRelativeEntropyNats rho.coefficients sigma.coefficients
      ∂(mu : Measure (State I))) =
    (∫⁻ rho : State I, extendedRelativeEntropyNats rho.coefficients (averageCoefficients mu)
      ∂(mu : Measure (State I))) +
        extendedRelativeEntropyNats (averageCoefficients mu) sigma.coefficients := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
