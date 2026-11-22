-- Prove2me | Theorems.Thm_SchauderBasis_tendstoUniformly_iteratedDeriv_fourier_partialSum
-- name    : SchauderBasis.tendstoUniformly_iteratedDeriv_fourier_partialSum
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:54.991802+00:00
-- url     : https://prove2.me/theorems/bf94951e-8ff0-4ca5-a2a6-28d5376c6492
-- title:
--   Fourier series of a smooth periodic function converge in the $C^\infty$ topology: every derivative of the partial sums converges uniformly
-- statement:
--   **Fourier series of smooth periodic functions converge in the $C^\infty$ topology.** Let $T>0$ and let $\varphi:\mathbb R\to\mathbb C$ be a $C^\infty$ function of period $T$, with Fourier coefficients
--   $$\widehat\varphi(m)=\frac1T\int_0^T\varphi(t)\,e^{-2\pi imt/T}\,dt\qquad(m\in\mathbb Z).$$
--   Then for every integer $k\ge0$ the $k$-th derivatives of the finite partial sums of the Fourier series converge to $\varphi^{(k)}$ uniformly on $\mathbb R$, along the directed set of finite subsets $s\subset\mathbb Z$:
--   $$\sup_{t\in\mathbb R}\Big|\frac{d^k}{dt^k}\sum_{m\in s}\widehat\varphi(m)\,e^{2\pi imt/T}-\varphi^{(k)}(t)\Big|\xrightarrow[s\uparrow\mathbb Z]{}0 .$$
--   In other words the Fourier series (4.1.1.1) of a function in $C^\infty(\mathbb T)$ converges unconditionally in the smooth (Fréchet) topology of $C^\infty(\mathbb T)$, the topology of uniform convergence of all derivatives. This is the convergence that makes the exponential system a Schauder basis of $C^\infty(\mathbb T)$, the model example of the paper's Chapter 4 (pp. 156–158).
--
--   **Formalization Note.** Functions on $\mathbb T=\mathbb R/T\mathbb Z$ are represented by their $T$-periodic lifts to $\mathbb R$; `fourierCoeffOn hT φ m` is $\widehat\varphi(m)$ computed on $[0,T]$, and `fourier m (t : AddCircle T)` is $e^{2\pi imt/T}$. Convergence along `atTop` in `Finset ℤ` is unconditional convergence and implies convergence of the symmetric partial sums. `∞` is the smoothness exponent $C^\infty$ (`open scoped ContDiff`). The circle has an arbitrary period $T>0$ (the paper takes $T=1$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 156–157, §4.1.1, (4.1.1.1) and the sentence following it; classical reference: G. B. Folland, Fourier Analysis and Its Applications, Wadsworth & Brooks/Cole, 1992, Ch. 2, §2.3, Thm. 2.6, p. 41 (as cited by the paper)

import Mathlib

open Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace SchauderBasis

theorem tendstoUniformly_iteratedDeriv_fourier_partialSum
    (T : ℝ) (hT : 0 < T) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hper : Function.Periodic φ T)
    (k : ℕ) :
    TendstoUniformly
      (fun s : Finset ℤ => iteratedDeriv k (fun t : ℝ =>
        ∑ m ∈ s, fourierCoeffOn hT φ m * fourier m (t : AddCircle T)))
      (iteratedDeriv k φ) atTop := by sorry

end SchauderBasis
