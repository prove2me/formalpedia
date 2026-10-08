-- Prove2me | Theorems.Thm_RegevLWE_GaussConv_eq_11
-- name    : RegevLWE.GaussConv.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:28.489374+00:00
-- url     : https://prove2.me/theorems/a2a5400d-5136-4774-89d7-ee08ebedf279
-- title:
--   Eq. (11), p. 34:25 — completing the square: Y(x) = (1/sⁿ)ρ_t(x)·ρ_{rs/t,(r/t)²x−u}(L)/ρ_{r,−u}(L)
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice, $u \in \mathbb{R}^n$, $r, s > 0$, and $t := \sqrt{r^2 + s^2}$. Let $Y$ be the density of the sum of a sample of $D_{L+u,r}$ and an independent sample of $\nu_s$, $Y(x) = \sum_{y \in L+u} D_{L+u,r}(y)\,\nu_s(x - y)$. Then for every $x \in \mathbb{R}^n$,
--   $$Y(x) = \frac{1}{s^n}\,\rho_t(x)\cdot\frac{\rho_{rs/t,\,(r/t)^2x - u}(L)}{\rho_{r,-u}(L)} .$$
--
--   This is the completing-the-square part of the chain (11) in the proof of Claim 3.9: it rewrites the density of $Y$ as the continuous Gaussian $\rho_t(x)/s^n$ times a ratio of two shifted Gaussian sums over $L$, to which Poisson summation is then applied.
--
--   **Formalization Note** $\rho_{\sigma,c}(L) = \sum_{x \in L}\rho_\sigma(x - c)$, so $\rho_{r,-u}(L) = \rho_r(L + u)$. The statement formalizes the equality of the first and fifth lines of the printed chain (11); the last two lines (the same ratio after Poisson summation, Lemma 2.14) are not part of this item.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:25, proof of Claim 3.9, chain (11), first to fifth line

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace RegevLWE.GaussConv

theorem eq_11 {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (u x : EuclideanSpace ℝ (Fin n)) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Ydensity L u r s x =
      1 / s ^ n * rho (Real.sqrt (r ^ 2 + s ^ 2)) x *
        (rhoShiftLattice (r * s / Real.sqrt (r ^ 2 + s ^ 2))
            ((r / Real.sqrt (r ^ 2 + s ^ 2)) ^ 2 • x - u) L /
          rhoShiftLattice r (-u) L) := by sorry

end RegevLWE.GaussConv
