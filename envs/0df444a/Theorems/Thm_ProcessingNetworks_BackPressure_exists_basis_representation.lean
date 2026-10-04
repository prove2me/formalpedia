-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_exists_basis_representation
-- name    : ProcessingNetworks.BackPressure.exists_basis_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:21:44.1582+00:00
-- url     : https://prove2.me/theorems/7cca03e5-2e57-4664-87c3-d4b0d0f6dbd4
-- title:
--   Lemma 9.3 — existence of a basis representation (milestone)
-- statement:
--   **Lemma 9.3.** Given Assumption 9.1, let $y > 0$ with $Rx=y$ for some $x \in
--   \mathbb{R}^J_+$. Then there is a basis with matrix $\hat R$ and $\hat x \in \mathbb{R}^I_+$
--   such that $\hat R \hat x = y$.
--
--   This is the technical bridge letting a feasible material-balance solution over all $J$
--   activities be re-expressed using only $I$ "basic" ones — used directly in Proposition 9.4's
--   proof.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 165, Lemma 9.3

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork

namespace ProcessingNetworks.BackPressure

/-- Lemma 9.3, Dai & Harrison p. 165 (PDF p. 181): given that Assumption 9.1 holds, let `y > 0`
be such that `Rx = y` for at least one `x ∈ ℝ^J_+`. Then there exist a basis and a vector
`x̂ ∈ ℝ^I_+` such that `R̂x̂ = y` (9.4). -/
theorem exists_basis_representation
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (y : Fin I → ℝ) (hy : ∀ i, 0 < y i)
    (x : Fin J → ℝ) (hx : ∀ j, 0 ≤ x j) (hRx : dat.R.mulVec x = y) :
    ∃ (basis : ActivityBasis dat) (xhat : Fin I → ℝ),
      (∀ i, 0 ≤ xhat i) ∧ (basisMatrix basis).mulVec xhat = y := by sorry

end ProcessingNetworks.BackPressure
