-- Prove2me | Theorems.Thm_RegevLWE_GaussConv_claim_3_8
-- name    : RegevLWE.GaussConv.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:19.002986+00:00
-- url     : https://prove2.me/theorems/370102ae-a532-4ab8-979a-2dac19455844
-- title:
--   Claim 3.8 — above the smoothing parameter, ρ_r(L + c) ∈ rⁿdet(L*)(1 ± ε)
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice, $c \in \mathbb{R}^n$, $\epsilon > 0$, and $r > 0$ with $r \ge \eta_\epsilon(L)$. Then
--   $$\rho_r(L + c) \in r^n \det(L^*)(1 \pm \epsilon), \quad\text{that is,}\quad \bigl|\rho_r(L + c) - r^n \det(L^*)\bigr| \le \epsilon\, r^n \det(L^*).$$
--
--   Above the smoothing parameter the Gaussian mass of a coset of $L$ is essentially independent of the shift $c$: the discrete Gaussian measure is nearly invariant under shifts. In Claim 3.9 it controls the normalization $\rho_r(L + u)$.
--
--   **Formalization Note** $\det(L^*)$ is written as $\det(L)^{-1}$, where $\det(L)$ is `ZLattice.covolume L` (the Lebesgue volume of a fundamental domain); the paper notes $\det(L^*) = 1/\det(L)$ (p. 34:17). The hypothesis $r > 0$ is added: $\rho_r$ is defined for $r > 0$ (Eq. (4)), and for $n \ge 1$ it already follows from $r \ge \eta_\epsilon(L) > 0$. $\epsilon > 0$ is printed.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:24, Claim 3.8

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace RegevLWE.GaussConv

theorem claim_3_8 {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (c : EuclideanSpace ℝ (Fin n)) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (h : smoothingParam L ε ≤ r) :
    |rhoCoset r L c - r ^ n * (ZLattice.covolume L)⁻¹| ≤
      ε * (r ^ n * (ZLattice.covolume L)⁻¹) := by sorry

end RegevLWE.GaussConv
