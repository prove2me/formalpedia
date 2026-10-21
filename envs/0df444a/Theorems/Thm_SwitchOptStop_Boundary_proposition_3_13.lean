-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_proposition_3_13
-- name    : SwitchOptStop.Boundary.proposition_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:52.822436+00:00
-- url     : https://prove2.me/theorems/6946aaba-87d6-4cb2-8297-f33427966aa1
-- title:
--   Proposition 3.13, p. 14 — V(ι, ·) ∈ W^{2,∞}((1/K, K)²) for every K > 1: ∂₁V, ∂₂V are Lipschitz on the square
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. For every regime $\iota$ and every $K>1$,
--   $$
--   V(\iota,\cdot)\in\mathscr W^{2,\infty}\big((1/K,K)^2\big),
--   $$
--   that is, the partial derivatives $\partial_1V(\iota,\cdot)$ and $\partial_2V(\iota,\cdot)$ are Lipschitz on the open square $(1/K,K)^2$.
--
--   This global second-order regularity is what the change-of-variable argument behind the integral equation (5.1) requires.
--
--   **Formalization Note** The Sobolev membership is stated in the paper's own reading (p. 11 and the last line of the proof): the first partial derivatives are uniformly Lipschitz on $(1/K,K)^2$. $V$ and $DV$ are then bounded on the square because its closure lies in $(0,\infty)^2$ and $V\in C^1$ there (Lemma 3.11).
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 14, Proposition 3.13 (reading of W^{2,∞} from p. 11)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Proposition 3.13 (p. 14): `V(ι, ·) ∈ W^{2,∞}((1/K, K)²)` for every `K > 1`, read as on p. 11: the
first partial derivatives of `V(ι, ·)` are Lipschitz on the open square `(1/K, K)²`. -/
theorem proposition_3_13 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∀ ι : Fin 2, ∀ K : ℝ, 1 < K → ∀ i : Fin 2, ∃ L : ℝ≥0,
      LipschitzOnWith L (pd i (value m S ι)) {x : Pt | ∀ j, 1 / K < x j ∧ x j < K} := by sorry

end SwitchOptStop.Boundary
