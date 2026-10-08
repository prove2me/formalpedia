-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_proposition_2_1
-- name    : SpikedWishart.SoftEdge.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:40:03.471388+00:00
-- url     : https://prove2.me/theorems/b4196a36-e1eb-4661-9597-c06addb36681
-- title:
--   Proposition 2.1, pp. 1655–1656 — P(λ₁ ≤ ξ) = det(1 − K_{M,N}) on L²((ξ,∞)) for the double contour kernel (62)
-- statement:
--   Let $1\le N\le M$, let $U$ be unitary and $\ell_1,\dots,\ell_N>0$, $\pi_j=\ell_j^{-1}$. Fix $q$ with $0<q<\min_j\pi_j$. Let $\Gamma$ be a counterclockwise circle with real centre enclosing $\pi_1,\dots,\pi_N$ and lying in $\{\mathrm{Re}\,z>q\}$, and $\Sigma$ a counterclockwise circle with real centre enclosing $0$ and lying in $\{\mathrm{Re}\,w<q\}$. Let $K_{M,N}$ be the kernel (62),
--   $$
--   K_{M,N}(\eta,\zeta)=\frac{M}{(2\pi i)^2}\oint_\Gamma dz\oint_\Sigma dw\,e^{-\eta M(z-q)+\zeta M(w-q)}\frac1{w-z}\Big(\frac zw\Big)^M\prod_{k=1}^N\frac{\pi_k-w}{\pi_k-z}.
--   $$
--   Then for every $\xi\ge0$,
--   $$
--   \mathbb P(\lambda_1\le\xi)=\det\big(1-K_{M,N}\big)_{L^2((\xi,\infty))},
--   $$
--   where $\lambda_1$ is the largest eigenvalue of the sample covariance matrix and the right side is the Fredholm series.
--
--   This exact finite-$N$ formula is the starting point of the asymptotic analysis: Theorem 1.1 follows by rescaling $\eta,\zeta$ around the edge and passing to the limit in the kernel.
--
--   **Formalization Note** The paper states (63) for every $\xi\in\mathbb R$, but its kernel lives on $L^2((0,\infty))$ (the projection $P_\xi$ "from $(0,\infty)$ to $(\xi,\infty)$", p. 1657): for $\xi<0$, $\mathbb P(\lambda_1\le\xi)=0$ while the determinant of the polynomially extended kernel is not $0$ (at $N=1$, $M=3$, $\ell_1=2$, $\xi=-1/2$ it is about $-0.125$). The statement is therefore made for $\xi\ge0$. $N\le M$ is the paper's standing assumption (density (59) involves $(\det S)^{M-N}$). The contours are circles with real centres; the kernel is real and its real part is taken. The case of coinciding $\pi_j$ is included (the paper obtains it by l'Hôpital's rule).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1655–1656, Proposition 2.1, (62)–(63)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Model
import Definitions.Def_SpikedWishart_SoftEdge_Airy
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem proposition_2_1 (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (q : ℝ) (hq0 : 0 < q) (hq : ∀ j, q < (ℓ j)⁻¹)
    (cΓ ρΓ : ℝ) (hΓ_encl : ∀ j, |(ℓ j)⁻¹ - cΓ| < ρΓ) (hΓ_right : q < cΓ - ρΓ)
    (cS ρS : ℝ) (hS_encl : |cS| < ρS) (hS_left : cS + ρS < q)
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    (sampleLaw M N).real {G | largestEig M U ℓ G ≤ ξ} =
      fredholmDet (kernelKMN M (fun j => (ℓ j)⁻¹) q cΓ ρΓ cS ρS) ξ := by sorry

end SpikedWishart.SoftEdge
