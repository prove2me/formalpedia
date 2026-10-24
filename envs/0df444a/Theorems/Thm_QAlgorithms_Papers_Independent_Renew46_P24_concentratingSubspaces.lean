-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_concentratingSubspaces
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.concentratingSubspaces
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:47:49.085504+00:00
-- url     : https://prove2.me/theorems/709e59bb-aa0e-420d-9b93-e522cce21968
-- title:
--   Lemma 3.2: exponentially concentrating subspaces realize entropy density
-- statement:
--   Let $\omega^N(A)=\operatorname{Tr}(\sigma^NA)$ be normalized states with strictly positive densities on nonzero finite-dimensional complex Hilbert spaces, and let $X_k^N$ be uniformly bounded self-adjoint macroscopic observables. Assume exponential coordinate concentration at $x$: each fixed tolerance $\delta>0$ and coordinate $k$ has eventual spectral weight at least $1-e^{-C_k(\delta)N}$, with $C_k(\delta)>0$. Assume also asymptotic equipartition: every fixed centered log-density window $[-\delta,\delta]$ has logarithmic weight divided by $N$ tending to zero.
--
--   There exist nonzero projections $P^N$ whose normalized trace states exponentially concentrate at $x$ and for which
--
--   $$\lim_{N\to\infty}\frac{\log\operatorname{Tr}P^N-S(\sigma^N)}N=0,\qquad S(\sigma^N)=-\operatorname{Tr}(\sigma^N\log\sigma^N).$$
--
--   No canonical entropy-optimality assumption is imposed. The finite-volume difference is taken before the limit, so this identity does not subtract infinite entropy densities. This supplies the entropy-realizing subspaces used for ensemble equivalence.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 10, Lemma 3.2: exponentially concentrating subspaces realize entropy density

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P24

open Filter

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

-- Exact primitives verified against the pinned accepted-library SHA256 catalogue.

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Dependency50.P21 (spectralFunction relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3.2, PDF pp.10-11, (3.7): no canonical optimality is assumed.
The limit is of each finite-volume entropy difference, not a difference of infinite limits. -/
theorem concentratingSubspaces {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S) (x : K → ℝ)
    (hrho : IsStateSequence rho) (hpositive : ∀ n, (rho n).PosDef)
    (hexponential : exponentiallyConcentrates S rho x)
    (hequipartition : asymptoticEquipartition rho) :
    ∃ P : OperatorSequence S, IsProjectionSequence P ∧
      exponentiallyConcentrates S (projectionDensity P) x ∧
      Tendsto (fun n => (Real.log (P n).trace.re - densityEntropyNats (rho n)) /
        (volume n : ℝ)) atTop (𝓝 (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
