-- Prove2me | Theorems.Thm_PosetMarginals_Chains_proposition_3
-- name    : PosetMarginals.Chains.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:38.616988+00:00
-- url     : https://prove2.me/theorems/1deb7f42-349c-401d-8870-8c2d0a673696
-- title:
--   Proposition 3 — Algorithm 1 terminates with a feasible (Q) solution
-- statement:
--   For every finite nonempty poset and parameters satisfying the standing conditions, Algorithm 1 reaches an iteration count $n^*$ at which its positive support is empty, with every earlier support nonempty. Its accumulated nonnegative subset weights satisfy the marginal equalities and every maximal-chain inequality of (Q):
--   $$X^{n^*+1}=\varnothing,\qquad\sigma\in\operatorname{Feas}(\mathcal Q).$$
--
--   This establishes both termination of the construction and feasibility of its output for the auxiliary optimization problem.
--
--   **Formalization Note** Lean state $n$ is after $n$ paper iterations, so $n=n^*$ at termination. The output adds weights if the same subset is selected more than once; this is the disclosed additive interpretation of A7.
-- source:
--   Dahan, Amin & Jaillet, arXiv:1811.08516v3, p. 17, Proposition 3; proof pp. 17–18

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Algorithm

namespace PosetMarginals.Chains

/-- Dahan, Amin and Jaillet, Proposition 3, p. 17. Lean state `n` follows `n` paper iterations. -/
theorem proposition_3 {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α]
    (ρ : α → ℝ) (π : Finset α → ℝ) (h : Standing ρ π) :
    ∃ n : ℕ, (iter ρ π n).X = ∅ ∧
      (∀ k < n, (iter ρ π k).X.Nonempty) ∧
      FeasibleQ ρ π (output ρ π n) := by sorry

end PosetMarginals.Chains
