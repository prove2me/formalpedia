-- Prove2me | Theorems.Thm_SubexpPermanent_Main_fact_4_10
-- name    : SubexpPermanent.Main.fact_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:03:11.737052+00:00
-- url     : https://prove2.me/theorems/0dff6af3-9fe1-4ed9-a2ad-c92271cdca94
-- title:
--   Fact 4.10 — $\Phi_A$ is convex on $\mathbb R^E$ and $\mu_y-P_y$ is a subgradient for every maximizing perfect matching $P_y$
-- statement:
--   Let $A$ be a nonnegative $n\times n$ matrix with $\operatorname{per}(A)>0$, $E$ its edge set, $B$ the polytope of nonnegative matrices supported on $E$ with unit row and column sums, and
--   $$\Phi_A(y)=\log Z(e^y)+\max_{M\text{ perfect}}\sum_{e\in M}(\log A_e-y_e)\qquad(y\in\mathbb R^E).$$
--   Then $\Phi_A$ is convex on $\mathbb R^E$. For any $y\in\mathbb R^E$, if $P_y$ is the incidence matrix of a perfect matching that maximizes $\langle\log A-y,P\rangle$ over $P\in B$, then
--   $$\mu_y-P_y\in\partial\Phi_A(y),$$
--   where $\mu_y$ is the vector of edge probabilities under weights $e^y$. This is the first-order information the projected subgradient method of §8 uses.
--
--   Differences from the source:
--
--   - encoding: vectors in ℝ^E indexed by the edges of E → functions on the subtype Edges A of pairs (i, j) in E; reason: the same space with the same coordinates
--   - generalization: A ∈ ℚ^{n×n}_{≥0} with per(A) > 0 (the permanent problem of §4.1) → every real nonnegative n × n matrix with per(A) > 0; reason: §6 and §8 apply Fact 4.10 to the real matrix Â = e^θ; the rational case is a special case
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 16, Fact 4.10

import Mathlib
import Definitions.Def_SubexpPermanent_Main_Objective
import Definitions.Def_SubexpPermanent_Main_Subgradient

namespace SubexpPermanent.Main

/-- Fact 4.10 (convexity and subgradients of the objective), p. 16. -/
theorem fact_4_10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hper : 0 < A.permanent) :
    ConvexOn ℝ Set.univ (Phi A) ∧
    ∀ (y : Edges A → ℝ) (σ : Equiv.Perm (Fin n)), IsPerfMatching A σ →
      (∀ P ∈ polytopeB A, dotProduct (logA A - y) P ≤ dotProduct (logA A - y) (incVec A σ)) →
      edgeProbA A y - incVec A σ ∈ subdiff (Phi A) y := by sorry

end SubexpPermanent.Main
