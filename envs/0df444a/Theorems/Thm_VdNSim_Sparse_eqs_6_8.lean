-- Prove2me | Theorems.Thm_VdNSim_Sparse_eqs_6_8
-- name    : VdNSim.Sparse.eqs_6_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:22.81418+00:00
-- url     : https://prove2.me/theorems/f80f2b5b-0493-4fc8-bb6b-83f043ca056b
-- title:
--   Eqs. (6)–(8), pp. 12–13 — the two importance-sampling expectations
-- statement:
--   Let $\sigma_i=\sum_x\alpha_i(x)\overline{\phi_{r_i(x)}}\psi_x$, where $(\alpha_i,r_i)$ is the $i$th column-data slot of $A$. Define $p_x=|\psi_x|^2$, $q_y=|\phi_y|^2$, and the functions $F_i,G_i$ of Eqs. (7)–(8), splitting according to $p_x\ge q_{r_i(x)}$ and its strict complement. Then
--
--   $$\sigma_i=\sum_x p_xF_i(x)+\sum_y q_yG_i(y).$$
--
--   The identity turns each contribution to the matrix element into expectations that can be estimated from the two sampling laws.
--
--   **Formalization Note** No state normalization is needed for this algebraic identity. The value of a quotient at a zero-probability outcome is zero; its weighted contribution is also zero.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, pp. 12–13, Eqs. (6)–(8)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Eqs. (6)–(8): the p- and q-weighted expectations sum to sigma_i. -/
theorem eqs_6_8 {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ)
    (i : Fin s) :
    (∑ x, D.α i x * star (ϕ (D.r i x)) * ψ x) =
      expect (prob ψ) (F ψ ϕ D i) + expect (prob ϕ) (G ψ ϕ D i) := by sorry

end VdNSim.Sparse
