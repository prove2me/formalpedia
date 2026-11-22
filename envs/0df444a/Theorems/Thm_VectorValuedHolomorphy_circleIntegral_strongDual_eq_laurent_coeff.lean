-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_circleIntegral_strongDual_eq_laurent_coeff
-- name    : VectorValuedHolomorphy.circleIntegral_strongDual_eq_laurent_coeff
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:46.643836+00:00
-- url     : https://prove2.me/theorems/4789c8dc-0d9c-44ae-8ec5-16220865fed2
-- title:
--   Lemma C.5.3.2 — Laurent coefficients of a vector-valued meromorphic function as contour integrals: $a_k=\frac{1}{2\pi i}\oint\frac{f(\xi)}{(\xi-\xi_0)^{k+1}}d\xi$ for all $k\in\mathbb Z$
-- statement:
--   **Laurent coefficients as contour integrals (Lemma C.5.3.2).** Let $E$ be a Hausdorff locally convex space over $\mathbb C$ (in the source: quasi-complete), $U\subset\mathbb C$ open, $z_0\in U$, and let $f\colon U\setminus\{z_0\}\to E$ be holomorphic and meromorphic at $z_0$, with Laurent expansion
--   $$f(z)=\sum_{k\ge -N}a_k\,(z-z_0)^{k}\qquad(0<|z-z_0|<R)$$
--   for some integer $N\ge 0$, vectors $a_k\in E$ and $R>0$, the series converging in $E$ uniformly on the compact subsets of the punctured disc; put $a_k=0$ for $k<-N$. Let $C$ be a circle such that the closed disc bounded by $C$ is contained in $U$ and contains $z_0$ in its interior. Then for **every** $k\in\mathbb Z$,
--   $$a_k=\frac{1}{2\pi i}\oint_{C}\frac{f(z)}{(z-z_0)^{k+1}}\,dz ,$$
--   the integral being a weak (Pettis) integral: for every continuous linear form $\ell\in E'$,
--   $$\oint_{C}\frac{\ell(f(z))}{(z-z_0)^{k+1}}\,dz=2\pi i\,\ell(a_k).$$
--   For $k=-1$ this is the residue formula, for $k\ge 0$ and $N=0$ the Cauchy formula for the Taylor coefficients, and for $k<-N$ it says that the integral vanishes.
--
--   When $E$ is quasi-complete the integral exists as an element of $E$ (the integrand is continuous on the circle), and the identity holds in $E$, as stated in the source. The lemma is the basis of the residue calculus for vector-valued meromorphic functions (zeta integrals with values in spaces of distributions).
--
--   **Formalization Note.** `f : ℂ → E` is a total function with `DifferentiableOn ℂ f (U \ {z₀})`; the circle is `C(c, ρ)` with `closedBall c ρ ⊆ U` and `z₀ ∈ ball c ρ`, and `∮` is Mathlib's `circleIntegral` of the scalar function `z ↦ ℓ (f z) / (z - z₀) ^ (k + 1)` (integer power). The Laurent expansion is encoded as in the published `VectorValuedHolomorphy.meromorphicAt_iff_exists_laurent`: coefficients `a : ℕ → E` with a shift, `a j` being the coefficient of $(z-z_0)^{j-N}$, and `TendstoUniformlyOn` of the partial sums on every compact `K ⊆ ball z₀ R \ {z₀}`. Hence the coefficient of $(z-z_0)^k$ is `a (k + N).toNat` if `0 ≤ k + N` and `0` otherwise, which is the right-hand side `2 * π * Complex.I * ℓ (if 0 ≤ k + N then a (k + N).toNat else 0)`. The identity is stated through all continuous linear functionals, which determines the integral as an element of $E$ when it exists; in this weak form quasi-completeness is not needed and is not assumed (`[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]`). The source allows any closed positively oriented simple curve enclosing $z_0$ and no other pole; circles are formalized.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 739-740, Lemma C.5.3.2, formula (C.5.3.3)

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- Laurent coefficients as contour integrals: if `f` is holomorphic on `U \ {z₀}` and
`f z = ∑_j (z - z₀) ^ (j - N) • a j` near `z₀`, then for every `k : ℤ` the coefficient of
`(z - z₀) ^ k` is `(2πi)⁻¹ ∮ f z / (z - z₀) ^ (k + 1) dz` (tested against every continuous linear
functional), over any circle in `U` with `z₀` inside. -/
theorem circleIntegral_strongDual_eq_laurent_coeff {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E} {z₀ c : ℂ} {ρ : ℝ}
    (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ) (hf : DifferentiableOn ℂ f (U \ {z₀}))
    {N : ℕ} {a : ℕ → E} {R : ℝ} (hR : 0 < R)
    (ha : ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
      TendstoUniformlyOn
        (fun (n : ℕ) (z : ℂ) => ∑ j ∈ Finset.range n, (z - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j)
        f atTop K)
    (ℓ : StrongDual ℂ E) (k : ℤ) :
    (∮ z in C(c, ρ), ℓ (f z) / (z - z₀) ^ (k + 1)) =
      2 * π * Complex.I * ℓ (if 0 ≤ k + (N : ℤ) then a (k + (N : ℤ)).toNat else 0) := by sorry

end VectorValuedHolomorphy
