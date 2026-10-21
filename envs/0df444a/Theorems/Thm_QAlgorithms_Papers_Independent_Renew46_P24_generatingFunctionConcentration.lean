-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_generatingFunctionConcentration
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.generatingFunctionConcentration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:45:30.424946+00:00
-- url     : https://prove2.me/theorems/3a5da87d-f878-4ee7-a7c2-267c4d6f741e
-- title:
--   §3 remarks: differentiable generating functions imply exponential concentration
-- statement:
--   Let $X_k^N$ be uniformly bounded self-adjoint observables on nonzero finite-dimensional complex Hilbert spaces, and let $\omega^N$ be normalized states. For each $k$, suppose the finite real limit
--
--   $$\psi_k(t)=\lim_{N\to\infty}\frac1N\log\omega^N(e^{tNX_k^N})$$
--
--   exists on a neighborhood of $0$, and that $\psi_k$ is differentiable at $0$. Set $x_k=\psi_k'(0)$. Then for every $\delta>0$ and every $k$ there exist $C_k(\delta)>0$ and $N_k(\delta)$ such that
--
--   $$\omega^N\!\left(1_{[x_k-\delta,x_k+\delta]}(X_k^N)\right)\ge1-e^{-C_k(\delta)N}\qquad(N>N_k(\delta)).$$
--
--   The constants may depend on $k$ and $\delta$, but not on $N$. Only individual generating functions are required; no joint generating function or regularity away from zero is assumed. This is a criterion for the exponential-concentration hypothesis of Theorem 3.1.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 9, §3 remarks: differentiable generating functions imply exponential concentration

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

/-- PDF p.9, (3.3): existence near zero and differentiability at zero of each
single-coordinate generating function imply exponential concentration at its derivative. -/
theorem generatingFunctionConcentration {K : Type*} (S : MacroscopicSystem K)
    (hS : IsMacroscopic S) (rho : OperatorSequence S)
    (hrho : IsStateSequence rho)
    (hexists : ∀ k, ∀ᶠ t : ℝ in 𝓝 0, ∃ z : ℝ,
      Tendsto (generatingSequence S rho k t) atTop (𝓝 z))
    (hdiff : ∀ k, DifferentiableAt ℝ (generatingFunction S rho k) 0) :
    exponentiallyConcentrates S rho
      (fun k => deriv (generatingFunction S rho k) 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
