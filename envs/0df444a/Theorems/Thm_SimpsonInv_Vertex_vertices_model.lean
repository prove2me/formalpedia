-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_vertices_model
-- name    : SimpsonInv.Vertex.vertices_model
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:04.887568+00:00
-- url     : https://prove2.me/theorems/0f836c66-8e05-4e0f-a509-1470b73ec837
-- title:
--   Meaning of the theorem, p. 869 — with S₀ = Sₙ = 0 and Tᵢ > 0, D has exactly 2ⁿ⁻¹ vertices, the all-or-nothing modes
-- statement:
--   Consider Simpson's model with $S_0 = S_n = 0$ and positive processing times $T_1, \dots, T_n > 0$, with $n = m + 1$ operations, and let
--   $$
--   D = \{ (S_1, \dots, S_{n-1}) : S_i \ge 0,\ S_{i-1} - S_i + T_i \ge 0 \}.
--   $$
--   Then the vertices (extreme points) of $D$ are exactly the points of $D$ at which every service time is either $0$ or $S_{i-1} + T_i$:
--   $$
--   \operatorname{ext} D = \{ S \in D : \forall i \in \{1, \dots, n-1\},\ S_i = 0 \ \text{or}\ S_i = S_{i-1} + T_i \},
--   $$
--   and there are exactly $2^{n-1}$ of them.
--
--   This is why a manager "has to examine only $2^{n-1}$ possible modes": by THEOREM I the cheapest mode is one of these vertices.
--
--   **Formalization Note** Vertex means extreme point (`Set.extremePoints ℝ D`). The number of extreme points is `Set.ncard`, which also forces the set to be finite since $2^m \ne 0$. The hypothesis $T_i > 0$ is the paper's "the processing times $T_i$ are always positive" (p. 868), and $S_0 = S_n = 0$ its standing choices on p. 865. Lean index $j$ is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 869, Meaning of the theorem; model conventions p. 865 and p. 868

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem vertices_model {m : ℕ} (T : ℕ → ℝ) (hT : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < T i) :
    Set.extremePoints ℝ (dom (m := m) T 0 0) =
        {S : Fin m → ℝ | ∀ j : Fin m, S j = 0 ∨ S j = extVec 0 0 S j.val + T (j.val + 1)} ∩
          dom (m := m) T 0 0 ∧
      (Set.extremePoints ℝ (dom (m := m) T 0 0)).ncard = 2 ^ m := by sorry

end SimpsonInv.Vertex
