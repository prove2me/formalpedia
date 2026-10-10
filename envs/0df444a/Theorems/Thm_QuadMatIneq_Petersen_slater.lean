-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_slater
-- name    : QuadMatIneq.Petersen.slater
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:44.189659+00:00
-- url     : https://prove2.me/theorems/7ed98f07-dd84-48ce-9e6a-2a81c67413f3
-- title:
--   Proof of Proposition 4.16(b), p. 17 — $\bar F>0$ and $G\neq0$ imply that $N$ of (4.17) has a positive eigenvalue
-- statement:
--   Let $\bar F\in\mathbb R^{q\times q}$ with $\bar F>0$ and $G\in\mathbb R^{q\times n}$ with $G\neq0$, and let
--   $$N=\begin{bmatrix}G^\top\bar FG&0\\0&-I_p\end{bmatrix}$$
--   be the matrix of (4.17). Then $N$ has at least one positive eigenvalue.
--
--   This verifies the Slater condition of the matrix S-lemma (Theorem 4.7) in the non-strict Petersen lemma.
--
--   **Formalization Note** The symmetry of $N$ is passed as a hypothesis so that its eigenvalues can be named; it is always satisfied, because $\bar F$ is symmetric.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.5.3, proof of Proposition 4.16(b), p. 17 ("Note that the conditions of that theorem are satisfied since F̄ > 0 and G ≠ 0 imply that N has at least one positive eigenvalue.")

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

namespace QuadMatIneq.Petersen
open Matrix
theorem slater {n p q : ℕ} (Fbar : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin q) (Fin n) ℝ)
    (hFbar : Fbar.PosDef) (hG : G ≠ 0)
    (hN : (petersenN (p := Fin p) Fbar G).IsHermitian) :
    ∃ i, 0 < hN.eigenvalues i := by sorry
end QuadMatIneq.Petersen
