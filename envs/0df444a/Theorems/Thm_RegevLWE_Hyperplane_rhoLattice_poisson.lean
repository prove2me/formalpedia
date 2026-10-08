-- Prove2me | Theorems.Thm_RegevLWE_Hyperplane_rhoLattice_poisson
-- name    : RegevLWE.Hyperplane.rhoLattice_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:12.968885+00:00
-- url     : https://prove2.me/theorems/1f6a4515-3add-42f2-b37e-10ecf28a258f
-- title:
--   Proof of Lemma 3.15, p. 34:31 — ρ_r(L) = det(L*) rⁿ ρ_{1/r}(L*) ≥ det(L*) rⁿ
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice with dual $L^*$, and let $r > 0$. Then
--   $$\rho_r(L) = \det(L^*)\, r^n\, \rho_{1/r}(L^*) \;\ge\; \det(L^*)\, r^n .$$
--
--   The equality is Poisson summation (Lemma 2.14) applied to $\rho_r$, whose Fourier transform is $r^n\rho_{1/r}$; the inequality keeps only the term $y = 0$ of the nonnegative sum $\rho_{1/r}(L^*)$. It lower-bounds the normalization of the discrete Gaussian $D_{L,r}$ at every width, with no smoothing hypothesis. The same display appears in the proofs of Lemmas 3.2 and 3.12.
--
--   **Formalization Note** $\det(L^*)$ is written as $\det(L)^{-1}$, where $\det(L)$ is `ZLattice.covolume L` (the Lebesgue volume of a fundamental domain); the paper notes $\det(L^*) = 1/\det(L)$ (p. 34:17). The hypothesis $r > 0$ is the paper's standing reading of a Gaussian width.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:31, proof of Lemma 3.15, sentence after the displayed chain ('By using Lemma 2.14 again, …')

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

namespace RegevLWE.Hyperplane

theorem rhoLattice_poisson {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {r : ℝ} (hr : 0 < r) :
    rhoLattice r L = (ZLattice.covolume L)⁻¹ * r ^ n * rhoDual (1 / r) L ∧
      (ZLattice.covolume L)⁻¹ * r ^ n ≤ rhoLattice r L := by sorry

end RegevLWE.Hyperplane
