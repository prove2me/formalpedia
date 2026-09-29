-- Prove2me | Theorems.Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq
-- name    : VectorFourier.fourierIntegral_flip_fourierIntegral_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a79f4737-dd45-5256-b188-cf1c00bdf91e
-- title:
--   Fourier inversion for a nondegenerate pairing and Haar measure
-- statement:
--   Let $V$ be a finite-dimensional real normed vector space equipped with its Borel $\sigma$-algebra, let $\mu$ be an additive Haar measure on $V$, let $B \colon V \times V \to \mathbb{R}$ be a bilinear form that is nondegenerate, let $b = (b_i)_{i \in \iota}$ be a basis of $V$ indexed by a finite type $\iota$, let $f$ be a Schwartz function on $V$ with values in $\mathbb{C}$, and let $x \in V$. The assertion is the identity
--   $$\mathcal{F}_{B^{t}}\bigl(\mathcal{F}_{B} f\bigr)(x) = \frac{\mu(P_b)^{2}}{\bigl|\det\bigl(B(b_i,b_j)\bigr)_{i,j}\bigr|}\, f(-x),$$
--   where $\mathcal{F}_{B}$ and $\mathcal{F}_{B^{t}}$ denote Mathlib's vector-valued Fourier integral `VectorFourier.fourierIntegral` taken with respect to $\mu$, the additive character $e(t) = e^{2\pi i t}$ and the pairings $B$ and its flip $B^{t}(x,y) = B(y,x)$ respectively, so that both transforms use the kernel $e(-B(\cdot,\cdot))$ with the same sign convention; $\mu(P_b)$ is the real-valued measure of the fundamental domain $P_b = \{\sum_i t_i b_i : 0 \le t_i < 1\}$ of the lattice spanned by $b$, the determinant is that of the Gram matrix of $B$ in the basis $b$, and the displayed real constant is viewed in $\mathbb{C}$. No symmetry of $B$ is assumed; when $B$ is symmetric the left-hand side is $\mathcal{F}_{B}\mathcal{F}_{B} f$.
--
--   This is Fourier inversion on a real vector space in basis-free form: the transform is taken with respect to an arbitrary Haar measure and an arbitrary nondegenerate bilinear pairing rather than an inner product and Lebesgue measure, and the resulting normalising constant $\mu(P_b)^2/|\det(B(b_i,b_j))|$ is recorded explicitly (it is independent of the basis, being the product of the covolumes of the lattice spanned by $b$ and its $B$-dual). It is used to obtain the injectivity statement that an integrable function all of whose $B$-Fourier integrals vanish is almost everywhere zero, and in the adelic setting to prove inversion for the Fourier transform of a pure tensor attached to the trace pairing of a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq.lean

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Module.ZLattice.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap

theorem VectorFourier.fourierIntegral_flip_fourierIntegral_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (f : 𝓢(V, ℂ)) (x : V) :
    VectorFourier.fourierIntegral 𝐞 μ B.flip (VectorFourier.fourierIntegral 𝐞 μ B f) x
      = ((μ.real (ZSpan.fundamentalDomain b)) ^ 2 / |(Matrix.of fun i j => B (b i) (b j)).det| : ℝ)
        * f (-x) := by sorry
