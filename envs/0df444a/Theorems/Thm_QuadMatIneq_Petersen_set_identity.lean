-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_set_identity
-- name    : QuadMatIneq.Petersen.set_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:49.854677+00:00
-- url     : https://prove2.me/theorems/63a2a013-bb97-44f7-96ec-26264767fa71
-- title:
--   Proof of Proposition 4.16, p. 17 — $\{FG: F^\top F\leqslant\bar F\}=\{S\bar F^{1/2}G: S^\top S\leqslant I\}=\{H: H^\top H\leqslant G^\top\bar FG\}$
-- statement:
--   Let $\bar F\in\mathbb R^{q\times q}$ with $\bar F\geqslant0$, let $\bar F^{1/2}$ be its positive semidefinite square root, and let $G\in\mathbb R^{q\times n}$. Then
--   $$\{FG\in\mathbb R^{p\times n}\mid F\in\mathbb R^{p\times q},\ F^\top F\leqslant\bar F\}=\{S\bar F^{1/2}G\in\mathbb R^{p\times n}\mid S\in\mathbb R^{p\times q},\ S^\top S\leqslant I\}$$
--   and this set equals
--   $$\{H\in\mathbb R^{p\times n}\mid H^\top H\leqslant G^\top\bar FG\}.$$
--
--   This is the first step of the paper's proof of Petersen's lemma: it replaces the products $FG$ over the norm-bounded uncertainty set by the solution set of a single quadratic matrix inequality in $H$.
--
--   **Formalization Note** The square root is Mathlib's `CFC.sqrt` for the (scoped) matrix order, which on a positive semidefinite matrix is its unique positive semidefinite square root. The sets are written as images of $F\mapsto FG$ and $S\mapsto S\bar F^{1/2}G$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.5.3, proof of Proposition 4.16, p. 17, first paragraph (the two set identities obtained from Lemma A.1)

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

open scoped MatrixOrder

namespace QuadMatIneq.Petersen
open Matrix
theorem set_identity {n p q : ℕ} (Fbar : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin q) (Fin n) ℝ)
    (hFbar : Fbar.PosSemidef) :
    (fun F : Matrix (Fin p) (Fin q) ℝ => F * G) '' uncSet Fbar =
        (fun S : Matrix (Fin p) (Fin q) ℝ => S * CFC.sqrt Fbar * G) ''
          {S | (1 - Sᵀ * S).PosSemidef} ∧
    (fun F : Matrix (Fin p) (Fin q) ℝ => F * G) '' uncSet Fbar =
        {H : Matrix (Fin p) (Fin n) ℝ | (Gᵀ * Fbar * G - Hᵀ * H).PosSemidef} := by sorry
end QuadMatIneq.Petersen
