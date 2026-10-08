-- Prove2me | Theorems.Thm_RegevLWE_SmoothingLB_claim_2_13
-- name    : RegevLWE.SmoothingLB.claim_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:13:19.842292+00:00
-- url     : https://prove2.me/theorems/2dafeb50-7a03-48a2-acac-b14a4e5a824f
-- title:
--   Claim 2.13 — η_ε(L) ≥ √(ln(1/ε)/π)·1/λ₁(L*) ≥ √(ln(1/ε)/π)·λ_n(L)/n
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice of dimension $n \ge 1$, with dual lattice $L^*$, and let $\epsilon > 0$. Let $\eta_\epsilon(L)$ be the smoothing parameter (the smallest $s$ with $\rho_{1/s}(L^*\setminus\{0\}) \le \epsilon$), $\lambda_1(L^*)$ the length of a shortest nonzero vector of $L^*$, and $\lambda_n(L)$ the smallest $r$ such that $L$ contains $n$ linearly independent vectors of length at most $r$. Then
--   $$\eta_\epsilon(L) \;\ge\; \sqrt{\frac{\ln 1/\epsilon}{\pi}}\cdot\frac{1}{\lambda_1(L^*)} \;\ge\; \sqrt{\frac{\ln 1/\epsilon}{\pi}}\cdot\frac{\lambda_n(L)}{n}.$$
--
--   This is the basic lower bound on the smoothing parameter: for any negligible $\epsilon$, $\eta_\epsilon(L)$ exceeds every constant multiple of $1/\lambda_1(L^*)$, and hence of $\lambda_n(L)/n$. It complements the upper bounds of Lemmas 2.11 and 2.12 and shows that the smoothing parameters used in Regev's reduction are within polynomial factors of the successive minima.
--
--   **Formalization Note** Both inequalities of the chain are stated (as a conjunction). The paper's "In particular" sentence, which is asymptotic ($\epsilon(n) = o(1)$, "for large enough $n$"), is not part of this statement. For $\epsilon \ge 1$ the paper's $\sqrt{\ln(1/\epsilon)/\pi}$ is the square root of a non-positive number; Lean's `Real.sqrt` returns $0$ there, so both inequalities reduce to $0 \le \eta_\epsilon(L)$ and $0 \le 0$, which are true; no hypothesis $\epsilon < 1$ is added, as the page says "any $\epsilon > 0$". The hypothesis $0 < n$ is the paper's convention that an $n$-dimensional lattice has $n \ge 1$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:20, Claim 2.13 (displayed chain)

import Mathlib
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

namespace RegevLWE.SmoothingLB

theorem claim_2_13 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (RegevLWE.GaussConv.dual L)) ≤ RegevLWE.GaussConv.smoothingParam L ε ∧
    Real.sqrt (Real.log (1 / ε) / Real.pi) * (lambdaN L / n) ≤
      Real.sqrt (Real.log (1 / ε) / Real.pi) * (1 / lambda1 (RegevLWE.GaussConv.dual L)) := by sorry

end RegevLWE.SmoothingLB
