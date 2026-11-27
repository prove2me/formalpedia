-- Prove2me | Theorems.Thm_RobustSAA_Discrete_Supplement_theorem_10
-- name    : RobustSAA.Discrete.Supplement.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:43:53.857791+00:00
-- url     : https://prove2.me/theorems/5612743c-f84c-4fa6-bb1a-e496824e6cdd
-- title:
--   Theorem 10 (corrected: CvM and AD vectors b, reversal Ĩ_N, Q ≥ 0) — the five univariate test constraints as conic constraints
-- statement:
--   Let $N\ge1$. The sets $K_{D_N},K_{V_N},K_{W_N},K_{U_N},K_{A_N}$ are convex cones, and for every $\zeta\in\mathbb R^N$:
--
--   1. $D_N(\zeta)\le Q\iff A_{D_N}\zeta-b_{D_N,\alpha}\in K_{D_N}$, for every $Q$;
--   2. $V_N(\zeta)\le Q\iff A_{V_N}\zeta-b_{V_N,\alpha}\in K_{V_N}$, for every $Q$;
--   3. $W_N(\zeta)\le Q\iff A_{W_N}\zeta-b_{W_N,\alpha}\in K_{W_N}$, for $Q\ge0$ with $Q^2\ge1/(12N^2)$;
--   4. $U_N(\zeta)\le Q\iff A_{U_N}\zeta-b_{U_N,\alpha}\in K_{U_N}$, for $Q\ge0$;
--   5. $A_N(\zeta)\le Q\iff A_{A_N}\zeta-b_{A_N,\alpha}\in K_{A_N}$, for $Q\ge0$,
--
--   where $Q=Q_{S_N}(\alpha)$ and the cones, matrices and vectors are those of the definition file (with the corrected entries $b_{W_N,\alpha,0}=-\sqrt{NQ^2-1/(12N)}$, $b_{A_N,\alpha,0}=e^{-(Q^2+1)/2}$ and $[\tilde I_N]_{ij}=\mathbb 1[i+j=N+1]$):
--
--   $$S_N(\zeta_1,\dots,\zeta_N)\le Q_{S_N}(\alpha)\iff A_{S_N}\zeta-b_{S_N,\alpha}\in K_{S_N}.$$
--
--   Applied with $\zeta_i=F_0(\xi^{(i)})$, this expresses each univariate confidence region through canonical cones, which is the input of the dualities of Theorems 11 and 12.
--
--   Differences from the source:
--   - reading: N data points → N ≥ 1; reason: the statistics divide by N and take maxima over i = 1, …, N
--   - correction: b_{W_N,α} = (√(N Q² − 1/(2N)), 1/(2N), …) → leading entry −√(N Q² − 1/(12N)); reason: (8) gives N W_N² = 1/(12N) + Σᵢ(ζᵢ − (2i−1)/(2N))²; since A_{W_N} has a zero first row, (Aζ − b)₀ = −b₀ must dominate ‖ζ − m‖₂; with the printed entry the cone condition never holds unless ζ = m (§10.14 omits the arithmetic)
--   - encoding: √(N Q_W² − 1/(12N)) in b_{W_N,α} → assumes Q ≥ 0 and Q² ≥ 1/(12N²); reason: excludes only thresholds below the minimum value 1/(√12·N) of W_N, where the square root is undefined and the region is empty
--   - correction: the W, U, A equivalences for every threshold → Q ≥ 0; reason: the statistics are nonnegative, while the cone conditions depend on Q only through Q², so a negative Q satisfies the cone side for some ζ but never the statistic side; excluded: negative thresholds, which quantiles of nonnegative statistics never are
--   - correction: b_{A_N,α} = (e^{−(Q_A)²−1}, 0, …, 0, −1, …, −1) → leading entry e^{−(Q²+1)/2}; reason: the cone exponents (2i−1)/(2N²) are half the weights (2i−1)/N² in (8), so the printed vector encodes A_N² ≤ 2Q² + 1; N = 1, ζ = ½, Q = ½: A₁² = 2 log 2 − 1 ≈ 0.386 > Q² but e^{−5/4} ≈ 0.287 ≤ (¼)^{1/2}
--   - correction: [Ĩ_N]_{ij} = 𝕀[i = N − j] → [Ĩ_N]_{ij} = 𝕀[i + j = N + 1] (1-based); reason: the printed relation leaves row N zero and refers to column 0; (8) pairs ζᵢ with 1 − ζ_{N+1−i}
--   - encoding: A_N with logarithms of ζᵢ, 1 − ζ_{N+1−i} → A_N ∈ [0, ∞], equal to +∞ unless every ζᵢ ∈ (0, 1); reason: a logarithm of a nonpositive number makes the statistic infinite; matches the published adStat
--   - encoding: vectors in ℝ^{2N}, ℝ^{N+1}, ℝ^{N+2}, ℝ^{2N+1} → functions on Fin N ⊕ Fin N, Option (Fin N), Option (Option (Fin N)), Option (Fin N ⊕ Fin N); reason: index sets only; the leading coordinate is `none`
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 10, pp. 17–18 (proof §10.14, p. 42)

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat

namespace RobustSAA.Discrete.Supplement

theorem theorem_10 (N : ℕ) (hN : 0 < N) :
    IsConvexCone (K_KS N) ∧ IsConvexCone (K_Kuiper N) ∧ IsConvexCone (K_CvM N) ∧
    IsConvexCone (K_Watson N) ∧ IsConvexCone (K_AD N) ∧
    (∀ (Q : ℝ) (ζ : Fin N → ℝ), ksZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_KS N Q ∈ K_KS N) ∧
    (∀ (Q : ℝ) (ζ : Fin N → ℝ),
      kuiperZ ζ ≤ Q ↔ (A_KS N).mulVec ζ - b_Kuiper N Q ∈ K_Kuiper N) ∧
    (∀ Q : ℝ, 0 ≤ Q → 1 / (12 * (N : ℝ) ^ 2) ≤ Q ^ 2 → ∀ ζ : Fin N → ℝ,
      cvmZ ζ ≤ Q ↔ (A_CvM N).mulVec ζ - b_CvM N Q ∈ K_CvM N) ∧
    (∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
      watsonZ ζ ≤ Q ↔ (A_Watson N).mulVec ζ - b_Watson N Q ∈ K_Watson N) ∧
    (∀ Q : ℝ, 0 ≤ Q → ∀ ζ : Fin N → ℝ,
      adZ ζ ≤ ENNReal.ofReal Q ↔ (A_AD N).mulVec ζ - b_AD N Q ∈ K_AD N) := by sorry

end RobustSAA.Discrete.Supplement
