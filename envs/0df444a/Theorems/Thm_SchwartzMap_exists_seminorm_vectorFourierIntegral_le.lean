-- Prove2me | Theorems.Thm_SchwartzMap_exists_seminorm_vectorFourierIntegral_le
-- name    : SchwartzMap.exists_seminorm_vectorFourierIntegral_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/3f127292-ef7a-53f4-86dc-40d57f7becf4
-- title:
--   Seminorm bound for the Fourier transform of a nondegenerate pairing
-- statement:
--   Let $V$ be a finite-dimensional real normed vector space equipped with a measurable space structure which is the Borel structure of its topology, let $\mu$ be an additive Haar measure on $V$, let $B$ be an $\mathbb{R}$-bilinear form on $V$ (a `LinearMap.BilinForm ℝ V`) which is nondegenerate, and let $k,n$ be natural numbers. The assertion is that there exist a finite set $s$ of pairs of natural numbers and a real constant $C \ge 0$ such that for every Schwartz function $f \in \mathcal{S}(V,\mathbb{C})$ there is a Schwartz function $g \in \mathcal{S}(V,\mathbb{C})$ whose underlying function is exactly the vector-valued Fourier integral of $f$ with respect to $\mu$, the pairing $B$ and the additive character $\mathbf{e}(t)=e^{2\pi i t}$, namely $y \mapsto \int_V \mathbf{e}(-B(v,y))\, f(v)\, d\mu(v)$, and such that the single Schwartz seminorm $p_{k,n}(g)$ is at most $C$ times the value at $f$ of the supremum over $s$ of Mathlib's Schwartz seminorm family. Thus $s$ and $C$ depend only on $(V,\mu,B,k,n)$ and not on $f$, while $g$, being the Fourier transform of $f$, depends on $f$; only the one seminorm indexed by $(k,n)$ is bounded, this being the seminorm form of continuity for that index.
--
--   This is the quantitative form of the statement that the Fourier transform attached to a nondegenerate real pairing and a Haar measure maps the Schwartz space $\mathcal{S}(V,\mathbb{C})$ continuously into itself: each Schwartz seminorm of $\mathcal{F}_B f$ is dominated by finitely many Schwartz seminorms of $f$. It is used in the analytic input to the study of the mixed embedding of a number field, in the bound for sums of norms of Fourier integrals over the ring of integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SchwartzMap_exists_seminorm_vectorFourierIntegral_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap

theorem SchwartzMap.exists_seminorm_vectorFourierIntegral_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (k n : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(V, ℂ), ∃ g : 𝓢(V, ℂ),
      ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f ∧
      SchwartzMap.seminorm ℝ k n g ≤ C * (s.sup (schwartzSeminormFamily ℝ V ℂ)) f := by sorry
