-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P12_gaussian_no_ideal_encoder
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P12.gaussian_no_ideal_encoder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:16:29.207995+00:00
-- url     : https://prove2.me/theorems/76e72fc1-934e-4a30-860c-748b0ac7d657
-- title:
--   §XII: symplectic operations cannot prepare ideal comb codewords
-- statement:
--   Let $N,n\ge1$ and $\alpha>0$. Start with a normalized $N$-mode pure Gaussian wavefunction whose complex symmetric quadratic matrix has positive definite real part. Apply any finite circuit of actual local Fourier transforms, real quadratic phases, distinct-mode beam mixing, finite positive squeezes and displacements. The output remains a normalized Gaussian $L^2$ wavefunction. If $T_\psi(f)=\int\psi(q)f(q)\,dq$ is its regular Schwartz functional and $J^{\otimes N}c$ is the tensor ideal comb with nonzero logical coefficient array $c$, then
--
--   $$T_\psi\ne J^{\otimes N}c.$$
--
--   Thus Gaussian symplectic circuitry, even with additional Gaussian modes, cannot prepare a nonzero ideal comb codeword. This is not a no-go theorem for finite-energy approximate encoders or for arbitrary photon-counting protocols.
-- source:
--   Encoding a qubit in an oscillator, arXiv:quant-ph/0008040v3, PDF p. 19, §XII: symplectic operations cannot prepare ideal comb codewords

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P12

noncomputable section

open scoped BigOperators

open MeasureTheory Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)

namespace QAlgorithms.Papers.Independent.Intakenext100.P12

/-- Section XII, PDF p.19: finite affine metaplectic circuits preserve normalized Gaussians
and cannot prepare a nonzero ideal comb codeword, even using additional Gaussian modes.
No claim about approximate encoders or adaptive photon counting is made. -/
theorem gaussian_no_ideal_encoder (N n : ℕ) (hN : 0 < N) (hn : 0 < n)
    (alpha : ℝ) (ha : 0 < alpha)
    (gates : List (GaussianGate N)) (hg : ∀ g ∈ gates, g.Valid)
    (psi : (Fin N → ℝ) → ℂ) (hpsi : IsGaussianWave N psi) :
    IsGaussianWave N (gaussianEval gates psi) ∧
    (∀ c : (Fin N → Fin n) → ℂ, c ≠ 0 →
      regularFunctional N (gaussianEval gates psi) ≠ tensorComb N n alpha c) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P12

end
