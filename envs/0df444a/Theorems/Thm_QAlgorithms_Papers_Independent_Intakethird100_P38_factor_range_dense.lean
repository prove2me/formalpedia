-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P38_factor_range_dense
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P38.factor_range_dense
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:26:44.221416+00:00
-- url     : https://prove2.me/theorems/bb10b3ca-acd3-4263-81a6-baaf4629f941
-- title:
--   Dense range of the constructed Hilbert factor
-- statement:
--   Let $n\ge1$, let $\mathcal S=\mathcal S(\mathbb R^n;\mathbb C)$ have its full Schwartz Fréchet topology, and write $\widehat\psi(u)=\int_{\mathbb R^n}e^{-iu\cdot x}\psi(x)\,dx$. Let $\mathcal C$ consist of the regular positive Borel measures $\sigma$ for which $\int(1+|u|^2)^{-p}\,d\sigma(u)<\infty$ for some nonnegative integer $p$.
--
--   Suppose $\sigma\in\mathcal C$, $L^2(\sigma)$ is infinite dimensional, and fix an isometric isomorphism $W:L^2(\sigma)\to L^2(dx)$. Assume that, for every compact $K\subset\mathbb R^n$, the complex linear span of $u\mapsto e^{it\cdot u}$, $t\in\mathbb R^n$, is dense in $L^2(K,\sigma)$. Define $Q\psi=W[\widehat\psi]_\sigma$. Then
--
--   $$\overline{Q(\mathcal S)}^{\,L^2(dx)}=L^2(dx).$$
--
--   The source's extra local-totality assumption is retained even though Schwartz density and Fourier inversion also imply this conclusion.
-- source:
--   Stochastic processes induced by singular operators, arXiv:1109.5273v1, PDF p. 11, Theorem 3.7: density of the factor range

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P38

open MeasureTheory Filter

open scoped Topology ComplexConjugate ENNReal

/-- Theorem 3.7, PDF p.11: dense range of the constructed factor, retaining
local totality of the exponential span and the fixed unitary W from (3.7). -/
theorem factor_range_dense (n : ℕ) (hn : 0 < n)
    (σ : Measure (SpectralDomain n)) (hσ : InC σ) (hinfinite : ¬ FiniteDimensional ℂ (L2 σ))
    (W : L2 σ ≃ₗᵢ[ℂ] L2 (volume : Measure (SpectralDomain n)))
    (htotal : LocallyTotalExponentials σ) :
    DenseRange (factorFromW W) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P38

end
