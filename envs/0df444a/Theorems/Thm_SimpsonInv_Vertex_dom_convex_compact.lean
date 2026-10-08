-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_dom_convex_compact
-- name    : SimpsonInv.Vertex.dom_convex_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:37.952286+00:00
-- url     : https://prove2.me/theorems/fa23770b-b5af-484f-a70f-cc3f95baa332
-- title:
--   The domain of the cost function, p. 868, and Appendix, p. 872 — D is convex and compact
-- statement:
--   Let $n = m + 1 \ge 1$, let $S_0, S_n$ and $T_1, \dots, T_n$ be real constants, and let $D \subseteq \mathbb R^{n-1}$ be the domain of Simpson's cost function:
--   $$
--   D = \{ (S_1, \dots, S_{n-1}) : S_i \ge 0 \ (1 \le i \le n-1),\ \ S_{i-1} - S_i + T_i \ge 0 \ (1 \le i \le n) \}.
--   $$
--   Then $D$ is a convex set and a compact subset of $\mathbb R^{n-1}$.
--
--   Convexity is the paper's "convex polyhedron" (an intersection of half-spaces), and compactness is what the Appendix uses to conclude that the cost function attains its minimum on $D$.
--
--   **Formalization Note** No hypothesis on the constants is needed: the empty set is convex and compact. $\mathbb R^{n-1}$ is `Fin m → ℝ` with its product (Euclidean) topology; Lean index $j$ is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 868, The domain of the cost function; p. 872, Appendix. Proof of Theorem I

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem dom_convex_compact {m : ℕ} (T : ℕ → ℝ) (S0 Sn : ℝ) :
    Convex ℝ (dom (m := m) T S0 Sn) ∧ IsCompact (dom (m := m) T S0 Sn) := by sorry

end SimpsonInv.Vertex
