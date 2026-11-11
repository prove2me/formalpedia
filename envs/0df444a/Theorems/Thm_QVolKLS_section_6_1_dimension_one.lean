-- Prove2me | Theorems.Thm_QVolKLS_section_6_1_dimension_one
-- name    : QVolKLS.section_6_1_dimension_one
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:40:04.424194+00:00
-- url     : https://prove2.me/theorems/cfc906df-06bf-40cb-b819-f409f28d41c3
-- title:
--   §6.1 — the case $d=1$: binary search with $O(\log(\kappa/\varepsilon))$ queries
-- statement:
--   In dimension one the volume problem is settled by binary search. There is an absolute constant $C>0$ such that for every rational $x_0\in\mathbb Q$, rationals $0<r\le R$ and $0<\varepsilon<\tfrac12$ (with $\kappa=R/r$ and $\ell$ the bit length of $x_0,r,R,\varepsilon$) there is one circuit over $\{H,T,\mathrm{CNOT}\}$ with membership-oracle calls that
--
--   1. makes at most $C\log(\kappa/\varepsilon)$ membership queries;
--   2. uses at most $C\big(\kappa(1+\ell)/\varepsilon\big)^C$ gates;
--   3. for every convex body (interval) $K\subset\mathbb R$ with $B(x_0,r)\subseteq K\subseteq B(x_0,R)$ outputs $\hat V\in[(1-\varepsilon)\mathrm{vol}(K),(1+\varepsilon)\mathrm{vol}(K)]$ with probability $1$.
--
--   The paper locates both endpoints of the interval to accuracy $\varepsilon r/4$ from the interior point; since the length is at least $2r$, the relative error is at most $\varepsilon$.
--
--   **Formalization Note** Stated in the model of the main theorem (`MemAlgorithm 1`). $\kappa/\varepsilon>2$, so the logarithm is positive.
--
--   Differences from the source:
--   - reading: binary searches … using O(log(κ/ε)) queries … this settles that case → the main theorem's model at d = 1: query bound C·log(κ/ε), gate bound C(κ(1+ℓ)/ε)^C, success probability 1; reason: 'settles that case' means Theorem 6.1 holds for d = 1; binary search is deterministic, so the probability is 1
--   - generalization: Theorem 6.1's inputs include ψ ≤ ψ_2 → no ψ among the inputs; the bit length is that of x₀, r, R, ε; reason: the d = 1 argument does not use ψ; adding ψ to the inputs only weakens the statement
--   - encoding: the oracle and output conventions of Theorem 6.1 → MemAlgorithm 1 (dyadic formats, unitary circuit measured at the end, dyadic output); reason: same model as the goal
--   - reading: B(x₀, r) ⊆ K ⊆ B(x₀, R) with B(x, r) not specified open or closed → open inner ball, closed outer ball; reason: the stronger of the readings: an open inner ball and a closed outer ball admit the most bodies
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §6.1, p.44 (the case d = 1)

import Definitions.Def_QVolKLS_MemAlgorithm

set_option autoImplicit false

namespace QVolKLS

open MeasureTheory

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **§6.1, the case `d = 1`**, p.44:
"For d = 1, binary searches from the given interior point locate the two interval endpoints to
accuracy εr/4 using O(log(κ/ε)) queries. Since its length is at least 2r, this settles that case."

Stated in the model of the main theorem (`MemAlgorithm 1`): there is an absolute `C > 0` such that for
every rational `x₀`, rationals `0 < r ≤ R` and rational `0 < ε < 1/2` one circuit over `{H, T, CNOT}`
makes at most `C log(κ/ε)` membership queries (`κ = R/r`), has at most `C (κ (1 + ℓ)/ε)^C` gates
(`ℓ` the bit length of `x₀, r, R, ε`), and for every convex body `K ⊆ ℝ` with
`B(x₀, r) ⊆ K ⊆ B(x₀, R)` outputs a value in `[(1 − ε) vol K, (1 + ε) vol K]` with probability `1`.

**Formalization Note.** Binary search is deterministic, so the success probability is `1`. The gate
clause is the main theorem's "remaining computation is polynomial", at `d = 1`; `ψ` is not used in
this case. `κ/ε > 2`, so the logarithm is positive. -/
theorem section_6_1_dimension_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x0 : Fin 1 → ℚ) (r R ε : ℚ), 0 < r → r ≤ R → 0 < ε → ε < 1 / 2 →
        ∃ A : MemAlgorithm 1,
          (A.queries : ℝ) ≤ C * Real.log (((R : ℝ) / (r : ℝ)) / (ε : ℝ)) ∧
          (A.gates : ℝ) ≤
              C * (((R : ℝ) / (r : ℝ)) *
                (1 + ((ratBitLen (x0 0) + ratBitLen r + ratBitLen R + ratBitLen ε : ℕ) : ℝ)) /
                  (ε : ℝ)) ^ C ∧
          ∀ K : Set (Euc 1), IsConvexBody K →
            Metric.ball (ratPoint x0) (r : ℝ) ⊆ K → K ⊆ Metric.closedBall (ratPoint x0) (R : ℝ) →
            A.outProb K
              (Set.Icc ((1 - (ε : ℝ)) * (volume K).toReal) ((1 + (ε : ℝ)) * (volume K).toReal)) = 1 := by sorry

end QVolKLS
