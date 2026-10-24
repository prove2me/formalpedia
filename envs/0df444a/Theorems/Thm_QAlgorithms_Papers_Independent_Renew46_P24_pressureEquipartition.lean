-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P24_pressureEquipartition
-- name    : QAlgorithms.Papers.Independent.Renew46.P24.pressureEquipartition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:47:06.297977+00:00
-- url     : https://prove2.me/theorems/cbaf72df-96de-422f-9a06-94ab203157d7
-- title:
--   §3 remarks: differentiable Gibbs pressure suffices for equipartition
-- statement:
--   Let $X_1^N,\ldots,X_q^N$ be uniformly bounded self-adjoint observables on nonzero finite-dimensional complex Hilbert spaces. For real parameters $\theta$, define $Z_\theta^N=\operatorname{Tr}\exp(N\sum_k\theta_kX_k^N)$. Suppose the finite pressure limit $p(\theta)=\lim_N N^{-1}\log Z_\theta^N$ exists on a neighborhood of a fixed real parameter $\lambda$, and is continuously differentiable at $\lambda$. Construct $\sigma_\lambda^N=\exp(N\sum_k\lambda_kX_k^N)/Z_\lambda^N$ and $\omega_\lambda^N(A)=\operatorname{Tr}(\sigma_\lambda^NA)$. With $B_\lambda^N=N^{-1}(\log\sigma_\lambda^N-\omega_\lambda^N(\log\sigma_\lambda^N)I)$, one has
--
--   $$\lim_{N\to\infty}\frac1N\log\omega_\lambda^N\!\left(1_{[-\delta,\delta]}(B_\lambda^N)\right)=0\qquad(\delta>0).$$
--
--   Logarithms are natural, with $\log0=-\infty$ for spectral masses. This gives equipartition for the fixed PLUS-sign Gibbs family. It does not supply exponential concentration of all the other noncommuting observables.
-- source:
--   Quantum Macrostates, Equivalence of Ensembles and an H-Theorem, arXiv:math-ph/0601027v2, PDF p. 9, §3 remarks: differentiable Gibbs pressure suffices for equipartition

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

/-- PDF pp.9-10, (3.6): locally existing pressure continuously differentiable
at the fixed real Gibbs parameter implies AEP for that constructed Gibbs family. -/
theorem pressureEquipartition {q : ℕ} (S : MacroscopicSystem (Fin q))
    (hS : IsMacroscopic S) (lambda : Fin q → ℝ)
    (hexists : ∀ᶠ theta : (Fin q → ℝ) in 𝓝 lambda, ∃ z : ℝ,
      Tendsto (pressureSequence S theta) atTop (𝓝 z))
    (hdiff : ContDiffAt ℝ 1 (pressure S) lambda) :
    asymptoticEquipartition (gibbsFamily S lambda) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P24

end
