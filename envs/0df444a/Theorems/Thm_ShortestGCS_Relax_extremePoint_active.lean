-- Prove2me | Theorems.Thm_ShortestGCS_Relax_extremePoint_active
-- name    : ShortestGCS.Relax.extremePoint_active
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:05.956982+00:00
-- url     : https://prove2.me/theorems/f307c2b7-22b4-4ad4-be34-878b36a4307b
-- title:
--   Proof of Lemma 7.4, p. 13 — at an extreme point of a polyhedron, m linearly independent inequalities are active
-- statement:
--   Let $\mathcal I$ be a finite index set and $\mathcal Y = \{y \in \mathbb R^m : c_i^\top y + d_i \ge 0 \text{ for all } i \in \mathcal I\}$. If $\hat y$ is an extreme point of $\mathcal Y$, then there is a subset $J \subseteq \mathcal I$ with $|J| = m$ such that the vectors $(c_j)_{j \in J}$ are linearly independent and
--
--   $$
--   c_j^\top \hat y + d_j = 0 \quad \text{for all } j \in J.
--   $$
--
--   Collecting these rows into a matrix $C \in \mathbb R^{m\times m}$ gives an invertible $C$ with $C\hat y + d = 0$, which is how the proof of Lemma 7.4 recovers $Z = x\hat y^\top$.
--
--   **Formalization Note** Extreme points are Mathlib's `Set.extremePoints`, not a predicate defined through active constraints. The paper's polytope is bounded; boundedness is not needed here and is dropped, which makes the statement stronger.
-- source:
--   arXiv:2101.11565v5, proof of Lemma 7.4, p. 13, second sentence

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- Proof of Lemma 7.4, arXiv:2101.11565v5, p. 13: at an extreme point `ŷ` of a polyhedron
`{y : cᵢᵀy + dᵢ ≥ 0 ∀ i ∈ ℐ}` (finite `ℐ`) there are `m` linearly independent inequalities active at `ŷ`. -/
theorem extremePoint_active {m : ℕ} {ι : Type*} [Fintype ι] (c : ι → Fin m → ℝ) (d : ι → ℝ)
    (yhat : Fin m → ℝ) (hyhat : yhat ∈ Set.extremePoints ℝ (polyhedron c d)) :
    ∃ J : Finset ι, J.card = m ∧ LinearIndependent ℝ (fun j : J => c j) ∧
      ∀ j ∈ J, c j ⬝ᵥ yhat + d j = 0 := by sorry

end ShortestGCS.Relax
