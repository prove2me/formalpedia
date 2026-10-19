-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P07_chi_lowerSemicontinuous_entropy_identity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P07.chi_lowerSemicontinuous_entropy_identity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:55:43.110169+00:00
-- url     : https://prove2.me/theorems/b9719b07-73a5-4c8b-b649-de42c6763b15
-- title:
--   Proposition 1: lower semicontinuity and entropy-difference formula
-- statement:
--   Let $\mathcal H$ and, when a channel is present, $\mathcal H^{\prime}$ be separable complex Hilbert spaces. Write $\mathfrak S(\mathcal H)$ for the positive trace-one operators with trace-norm topology, and $\mathcal P$ for its Borel probability measures with weak convergence. For $\pi\in\mathcal P$, let $\bar\rho(\pi)$ denote its barycenter. A channel $\Phi$ is a completely positive trace-preserving linear map on trace-class operators. Entropies and relative entropies below are nonnegative extended quantities in nats. For a constraint set $A$, let $\mathcal P_A=\{\pi:\bar\rho(\pi)\in A\}$, let $\chi_\Phi(\pi)=\int H(\Phi(\rho)\Vert\Phi(\bar\rho(\pi)))\,\pi(d\rho)$, and define $\bar C(\Phi;A)$ initially as the supremum of $\chi_\Phi$ over finite-support measures in $\mathcal P_A$. The functional $\chi_\Phi$ is lower semicontinuous on $\mathcal P$. For every $\pi$ with $H(\Phi(\bar\rho(\pi)))<\infty$,
--
--   $$\chi_\Phi(\pi)+\int H(\Phi(\rho))\,\pi(d\rho)=H(\Phi(\bar\rho(\pi))).$$
--
--   Under the finite-entropy hypothesis this is equivalent to the source’s entropy-difference formula. It avoids subtracting two infinite quantities.
-- source:
--   Continuous ensembles and the chi-capacity of infinite-dimensional channels, arXiv:quant-ph/0408176v1, PDF p. 4, Proposition 1: lower semicontinuity and entropy-difference formula

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07

noncomputable section

open MeasureTheory Filter

open scoped ENNReal Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier18.P07

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsBarycenter IsTraceClassChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, PDF pp.4-5: lower semicontinuity and the entropy-difference
formula. Under finite average output extendedEntropyNats the additive identity is exactly
that formula, while avoiding subtraction of infinities. -/
theorem chi_lowerSemicontinuous_entropy_identity {I J : Type}
    [Countable I] [Countable J]
    (Phi : Matrix I I ℂ → Matrix J J ℂ) (hPhi : IsTraceClassChannel Phi) :
    LowerSemicontinuous (ensembleHolevo Phi) ∧
      ∀ mu : GeneralizedEnsemble I, extendedEntropyNats (Phi (averageCoefficients mu)) < ⊤ →
        ensembleHolevo Phi mu +
          (∫⁻ rho : State I, extendedEntropyNats (Phi rho.coefficients)
            ∂(mu : Measure (State I))) = extendedEntropyNats (Phi (averageCoefficients mu)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P07

end
