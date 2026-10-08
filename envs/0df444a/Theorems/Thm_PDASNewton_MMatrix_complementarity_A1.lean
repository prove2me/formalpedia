-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_complementarity_A1
-- name    : PDASNewton.MMatrix.complementarity_A1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:54.744309+00:00
-- url     : https://prove2.me/theorems/2fb9ab95-9788-4592-9800-9cb06cbb177e
-- title:
--   Appendix A, (A.1), p. 20 — for k ≥ 1, λᵏᵢ = 0 or yᵏᵢ = ψᵢ for all i
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$, $f,\psi \in \mathbb{R}^n$, $c \in \mathbb{R}$, and let $(y^k,\lambda^k)_{k\ge0}$ be any run of the primal-dual active set algorithm from arbitrary initial data. Then for every $k \ge 1$ and every index $i$,
--   $$\lambda^k_i = 0 \quad\text{or}\quad y^k_i = \psi_i .$$
--
--   This is the complementarity property (A.1) on which the whole proof of Theorem 3.2 rests: after one iteration, every coordinate is either dual-free or primal-active.
--
--   **Formalization Note** No hypothesis on $A$ or on $c$ is needed and none is assumed. The bound $k \ge 1$ is essential, since $(y^0,\lambda^0)$ is arbitrary.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 20, Appendix A, proof of Theorem 3.2, (A.1)

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem complementarity_A1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ∀ i, lam k i = 0 ∨ y k i = ψ i := by sorry

end PDASNewton.MMatrix
