-- Prove2me | Theorems.Thm_RegevLWE_SmoothingLB_proof_display
-- name    : RegevLWE.SmoothingLB.proof_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:03.371973+00:00
-- url     : https://prove2.me/theorems/efdd3e0f-1473-4dd4-a5ff-e52dd04314b0
-- title:
--   Proof of Claim 2.13, p. 34:20 — with v ∈ L* of length λ₁(L*) and s = η_ε(L), ε = ρ_{1/s}(L* ∖ {0}) ≥ ρ_{1/s}(v) = exp(−π(sλ₁(L*))²)
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice of dimension $n \ge 1$ with dual $L^*$, let $\epsilon > 0$ and put $s := \eta_\epsilon(L)$. Then there is a nonzero vector $v \in L^*$ of length $\|v\| = \lambda_1(L^*)$, and for it
--   $$\epsilon = \rho_{1/s}(L^*\setminus\{0\}) \ \ge\ \rho_{1/s}(v) = \exp\bigl(-\pi(s\lambda_1(L^*))^2\bigr).$$
--
--   This is the displayed chain of the proof of Claim 2.13; solving $\exp(-\pi(s\lambda_1(L^*))^2) \le \epsilon$ for $s$ gives the first inequality of the claim.
--
--   **Formalization Note** The existence of a shortest nonzero dual vector ("Let $v \in L^*$ be a vector of length $\lambda_1(L^*)$") is part of the conclusion, since $\lambda_1$ is defined as an infimum. The hypothesis $0 < n$ is the paper's convention that a lattice is $n$-dimensional with $n \ge 1$; without it $L^*$ has no nonzero vector.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:20, proof of Claim 2.13 (displayed chain)

import Mathlib
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

namespace RegevLWE.SmoothingLB

theorem proof_display {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ RegevLWE.GaussConv.dual L, v ≠ 0 ∧ ‖v‖ = lambda1 (RegevLWE.GaussConv.dual L) ∧
      ε = RegevLWE.GaussConv.rhoDualNonzero (1 / RegevLWE.GaussConv.smoothingParam L ε) L ∧
      RegevLWE.GaussConv.rho (1 / RegevLWE.GaussConv.smoothingParam L ε) v ≤ RegevLWE.GaussConv.rhoDualNonzero (1 / RegevLWE.GaussConv.smoothingParam L ε) L ∧
      RegevLWE.GaussConv.rho (1 / RegevLWE.GaussConv.smoothingParam L ε) v =
        Real.exp (-Real.pi * (RegevLWE.GaussConv.smoothingParam L ε * lambda1 (RegevLWE.GaussConv.dual L)) ^ 2) := by sorry

end RegevLWE.SmoothingLB
