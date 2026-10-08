-- Prove2me | Theorems.Thm_StoneRegression_NearestNeighbor_proposition_10
-- name    : StoneRegression.NearestNeighbor.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:30.095273+00:00
-- url     : https://prove2.me/theorems/75049491-b579-4b22-b1c7-5702d284e032
-- title:
--   Proposition 10, p. 613 — rescaling coordinates by factors in [a, b] keeps a cone of 𝒱(d, a/b) acute
-- statement:
--   Let $0 < a \le b_j \le b$ for $1 \le j \le d$. Let $V \in \mathcal V(d, a/b)$, i.e. any two nonzero $u, v \in V$ satisfy $u\cdot v > (1 - a^2/(2b^2))\|u\|\|v\|$. Let $u, v \in V$ with $0 < \|u\| \le \|v\|$, and let $\tilde u_j = b_j u_j$, $\tilde v_j = b_j v_j$. Then
--   $$\|\tilde v\| > \|\tilde v - \tilde u\| .$$
--
--   This geometric fact says that after rescaling the coordinates, the shorter of two vectors in a narrow cone is still strictly closer to the longer one than the origin is. It is the step that bounds how many sample points can have a given point among their nearest neighbors.
--
--   **Formalization Note** The rescaling is the coordinatewise product `coordScale`; vectors live in `EuclideanSpace ℝ (Fin d)` with its Euclidean norm and inner product.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 10, p. 613

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_10 {d : ℕ} (a b : ℝ) (bv : Fin d → ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : V ∈ ConeFamily d (a / b))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) (hv : v ∈ V) (hu0 : 0 < ‖u‖) (huv : ‖u‖ ≤ ‖v‖) :
    ‖coordScale bv v - coordScale bv u‖ < ‖coordScale bv v‖ := by sorry

end StoneRegression.NearestNeighbor
