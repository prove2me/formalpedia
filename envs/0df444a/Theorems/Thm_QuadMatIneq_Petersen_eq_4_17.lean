-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_eq_4_17
-- name    : QuadMatIneq.Petersen.eq_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:57.097804+00:00
-- url     : https://prove2.me/theorems/ef7e80fa-240f-4b04-be07-95f84d69c193
-- title:
--   (4.17), p. 17 — (4.15a) iff $\mathcal Z_p(N)\subseteq\mathcal Z_p^+(M)$, (4.16a) iff $\mathcal Z_p(N)\subseteq\mathcal Z_p(M)$; $N\in\boldsymbol\Pi_{n,p}$, $N_{22}<0$
-- statement:
--   Let $C\in\mathbb R^{n\times n}$ be symmetric, $E\in\mathbb R^{n\times p}$, $\bar F\in\mathbb R^{q\times q}$ with $\bar F\geqslant0$, $G\in\mathbb R^{q\times n}$, and $\mathcal F=\{F\in\mathbb R^{p\times q}\mid F^\top F\leqslant\bar F\}$. Define, as in (4.17),
--   $$M:=\begin{bmatrix}-C&-E\\-E^\top&0\end{bmatrix},\qquad N:=\begin{bmatrix}G^\top\bar FG&0\\0&-I\end{bmatrix}.$$
--   Then:
--
--   1. $C+EFG+G^\top F^\top E^\top<0$ for all $F\in\mathcal F$ if and only if $\mathcal Z_p(N)\subseteq\mathcal Z_p^+(M)$;
--   2. $C+EFG+G^\top F^\top E^\top\leqslant0$ for all $F\in\mathcal F$ if and only if $\mathcal Z_p(N)\subseteq\mathcal Z_p(M)$;
--   3. $N\in\boldsymbol\Pi_{n,p}$;
--   4. $N_{22}<0$.
--
--   Here $\mathcal Z_p(\cdot)\subseteq\mathbb R^{p\times n}$ are the QMI solution sets with $q:=n$, $r:=p$ in the notation of Section 3. This reformulation turns both forms of Petersen's lemma into instances of the matrix S-lemmas.
--
--   **Formalization Note** In the paper the letters $q,r$ of Section 3 are here $n,p$; the QMI sets live in `Matrix (Fin p) (Fin n) ℝ`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.5.3, proof of Proposition 4.16, p. 17, display (4.17) and the sentences following it

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

namespace QuadMatIneq.Petersen
open Matrix
theorem eq_4_17 {n p q : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin p) ℝ)
    (Fbar : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin q) (Fin n) ℝ)
    (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef) :
    ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
        (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef) ↔
      ZSet (petersenN (p := Fin p) Fbar G) ⊆ ZPlus (petersenM C E)) ∧
    ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
        (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef) ↔
      ZSet (petersenN (p := Fin p) Fbar G) ⊆ ZSet (petersenM C E)) ∧
    InPi (petersenN (p := Fin p) Fbar G) ∧
    (-(petersenN (p := Fin p) Fbar G).toBlocks₂₂).PosDef := by sorry
end QuadMatIneq.Petersen
