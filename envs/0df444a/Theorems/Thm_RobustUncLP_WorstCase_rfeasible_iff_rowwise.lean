-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_rfeasible_iff_rowwise
-- name    : RobustUncLP.WorstCase.rfeasible_iff_rowwise
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:51:25.219461+00:00
-- url     : https://prove2.me/theorems/d35136d3-8eb8-48ad-a065-10d1c794bba7
-- title:
--   (8), §2.2, p. 4 — x is r-feasible iff aᵀx ≥ 0 for all a ∈ 𝒰_i, all i, and fᵀx = 1
-- statement:
--   Let $\mathcal U$ be any set of real $m\times n$ matrices, $f \in \mathbb R^{n}$, and let $\mathcal U_i$ be the set of $i$-th rows of the matrices in $\mathcal U$. A point $x \in \mathbb R^{n}$ is robust feasible, i.e. $Ax \ge 0$ for every $A \in \mathcal U$ and $f^{T}x = 1$, if and only if
--   $$a^{T}x \ge 0 \quad \forall a \in \mathcal U_i\ \forall i, \qquad f^{T}x = 1. \tag{8}$$
--
--   The robust counterpart therefore sees only the possible realizations of each constraint separately, and not the dependencies between constraints.
--
--   **Formalization Note** The paper states (8) in the context of constraint-wise uncertainty; the statement holds for every $\mathcal U$ and is formalized without that hypothesis (and without the standing convexity and closedness of $\mathcal U$), which makes it stronger.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 4, §2.2, (8)

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem rfeasible_iff_rowwise {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) :
    ∀ x : Fin n → ℝ, x ∈ robustFeas U f ↔
      (∀ i : Fin m, ∀ a ∈ rowProj U i, 0 ≤ a ⬝ᵥ x) ∧ f ⬝ᵥ x = 1 := by sorry

end RobustUncLP.WorstCase
