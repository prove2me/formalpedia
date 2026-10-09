-- Prove2me | Theorems.Thm_SymPolyOpt_PowerSumLB_schur_hankel_bound
-- name    : SymPolyOpt.PowerSumLB.schur_hankel_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:23.272161+00:00
-- url     : https://prove2.me/theorems/0d012163-5437-493f-8819-43f36e01fabf
-- title:
--   Proof of Theorem 6.6(b), p. 26 — Schur complement on H_{r+1}(s): s_{2r} ≥ uᵀ H_r(s)⁻¹ u
-- statement:
--   Let $s = (s_0, s_1, \dots)$ be a real sequence and $r \in \mathbb N$. Write
--   $$H_{r+1}(s) = \begin{pmatrix} H_r(s) & u \\ u^T & s_{2r} \end{pmatrix}, \qquad u^T = (s_r, \dots, s_{2r-1}).$$
--   If $H_{r+1}(s) \succeq 0$ and $H_r(s) \succ 0$, then
--   $$u^T H_r(s)^{-1} u \le s_{2r}.$$
--
--   This is the Schur-complement step that ends the proof of Theorem 6.6(b): once $s_0, \dots, s_{2r-1}$ are prescribed, it yields an explicit lower bound on the free entry $s_{2r}$.
--
--   **Formalization Note** The page only says "Schur's complement applied to the Hankel matrix $H_{r+1}(s)$". The bound uses the inverse $H_r(s)^{-1}$, which requires $H_r(s)$ to be invertible; positive definiteness of $H_r(s)$ is added for this. Without it Lean's matrix inverse would be the zero matrix.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 26, proof of Theorem 6.6(b), "the final result follows from Schur's complement applied to the Hankel matrix H_{r+1}(s)"

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting
open Matrix

namespace SymPolyOpt.PowerSumLB

/-- Schur complement on H_{r+1}(s) = [[H_r(s), u], [uᵀ, s_{2r}]] with u = (s_r, …, s_{2r−1}):
if H_{r+1}(s) ⪰ 0 and H_r(s) ≻ 0 then uᵀ H_r(s)⁻¹ u ≤ s_{2r}. -/
theorem schur_hankel_bound :
    ∀ (s : ℕ → ℝ) (r : ℕ), (hankel (r + 1) s).PosSemidef → (hankel r s).PosDef →
      (fun i : Fin r => s (r + i)) ⬝ᵥ ((hankel r s)⁻¹ *ᵥ fun i : Fin r => s (r + i))
        ≤ s (2 * r) := by sorry

end SymPolyOpt.PowerSumLB
