-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_eq_61
-- name    : SpikedWishart.SoftEdge.eq_61
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:40:33.527854+00:00
-- url     : https://prove2.me/theorems/fc3b9909-9f48-4627-9da5-fcdf7d32cc86
-- title:
--   (61), p. 1655 — joint density of the sample eigenvalues: det(e^{−Mπ_jλ_k})/V(π)·V(λ)·Πλ_j^{M−N}
-- statement:
--   Let $1\le N\le M$, let $U$ be an $N\times N$ unitary matrix and $\ell_1,\dots,\ell_N$ **distinct** positive reals, and set $\pi_j=\ell_j^{-1}$. Let $\lambda=(\lambda_1,\dots,\lambda_N)$ be the eigenvalues of the sample covariance matrix $S$ of the model, and
--   $$
--   p(\lambda)=\frac{\det\big(e^{-M\pi_j\lambda_k}\big)_{1\le j,k\le N}}{V(\pi)}\,V(\lambda)\prod_{j=1}^N\lambda_j^{M-N},\qquad V(x)=\prod_{i<j}(x_j-x_i).
--   $$
--   Then $p$, normalised on $(0,\infty)^N$, is the density of the unordered eigenvalues: for every bounded measurable symmetric function $\phi$ on $\mathbb R^N$,
--   $$
--   \mathbb E\,\phi(\lambda_1,\dots,\lambda_N)=\frac{1}{C}\int_{(0,\infty)^N}\phi(\lambda)\,p(\lambda)\,d\lambda,\qquad C=\int_{(0,\infty)^N}p(\lambda)\,d\lambda .
--   $$
--
--   This is the Harish-Chandra–Itzykson–Zuber form of the eigenvalue law of a complex Wishart matrix with general covariance; it is the starting point of the Fredholm formula of Proposition 2.1.
--
--   **Formalization Note** "Density of the eigenvalues" is encoded by its action on symmetric test functions, which is independent of how the eigenvalues are ordered. The case of coinciding $\pi_j$, which the paper interprets by l'Hôpital's rule, is not part of this statement; the $\pi_j$ are assumed distinct. $C>0$ is implicit: with $\phi=1$ the identity forces $C\ne0$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1655, §2.1, (61)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Model
import Definitions.Def_SpikedWishart_SoftEdge_Kernels
open MeasureTheory

namespace SpikedWishart.SoftEdge

theorem eq_61 (M N : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (hℓ : ∀ j, 0 < ℓ j) (hℓ_inj : Function.Injective ℓ)
    (f : (Fin N → ℝ) → ℝ) (hf : Measurable f) (hf_bdd : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hf_sym : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x) :
    ∫ G, f (sampleCov_isHermitian M U ℓ G).eigenvalues ∂(sampleLaw M N) =
      (∫ lam in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          f lam * eigDensity M (fun j => (ℓ j)⁻¹) lam) /
        ∫ lam in Set.pi Set.univ (fun _ : Fin N => Set.Ioi (0 : ℝ)),
          eigDensity M (fun j => (ℓ j)⁻¹) lam := by sorry

end SpikedWishart.SoftEdge
