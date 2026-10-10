-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_lemma_A_1
-- name    : QuadMatIneq.Petersen.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:31.81391+00:00
-- url     : https://prove2.me/theorems/8a2e25fd-24de-4289-8a3f-f37406e63493
-- title:
--   Lemma A.1, p. 26 — $A^\top A\leqslant B^\top B$ iff $A=SB$ with $S^\top S\leqslant I$; strict version under full column rank; $S:=AB^\dagger$ works
-- statement:
--   Let $A\in\mathbb R^{r\times q}$ and $B\in\mathbb R^{p\times q}$, and let $B^\dagger$ denote the Moore–Penrose pseudo-inverse of $B$.
--
--   1. $A^\top A\leqslant B^\top B$ if and only if there exists $S\in\mathbb R^{r\times p}$ with
--   $$A=SB\quad\text{and}\quad S^\top S\leqslant I. \tag{A.1}$$
--   2. If, in addition, $B$ has full column rank, then $A^\top A<B^\top B$ if and only if there exists $S\in\mathbb R^{r\times p}$ with
--   $$A=SB\quad\text{and}\quad S^\top S<I. \tag{A.2}$$
--   3. If $A^\top A-B^\top B\leqslant0$, then $S:=AB^\dagger$ satisfies (A.1).
--   4. If $A^\top A-B^\top B<0$, then $S:=AB^\dagger$ satisfies (A.2).
--
--   The lemma says that a Loewner-order bound between two Gram matrices is the same as a contractive factorization, with an explicit factor. In Petersen's lemma it converts the norm-bounded uncertainty $F^\top F\leqslant\bar F$ into a quadratic matrix inequality.
--
--   **Formalization Note** "$B$ has full column rank" is `B.rank = q`. Item 4 is stated without the full-column-rank hypothesis of item 2: the hypothesis $A^\top A<B^\top B$ already forces $B^\top B>0$, i.e. full column rank, so nothing is lost or added. $A^\top A\leqslant B^\top B$ is `(BᵀB − AᵀA).PosSemidef`, and $A^\top A-B^\top B\leqslant0$ is `(−(AᵀA − BᵀB)).PosSemidef`, the paper's two spellings of the same condition.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Lemma A.1, p. 26

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI

namespace QuadMatIneq.Petersen
open Matrix
theorem lemma_A_1 {p q r : ℕ} (A : Matrix (Fin r) (Fin q) ℝ) (B : Matrix (Fin p) (Fin q) ℝ) :
    ((Bᵀ * B - Aᵀ * A).PosSemidef ↔
        ∃ S : Matrix (Fin r) (Fin p) ℝ, A = S * B ∧ (1 - Sᵀ * S).PosSemidef) ∧
    (B.rank = q →
      ((Bᵀ * B - Aᵀ * A).PosDef ↔
        ∃ S : Matrix (Fin r) (Fin p) ℝ, A = S * B ∧ (1 - Sᵀ * S).PosDef)) ∧
    ((-(Aᵀ * A - Bᵀ * B)).PosSemidef →
      A = (A * pinv B) * B ∧ (1 - (A * pinv B)ᵀ * (A * pinv B)).PosSemidef) ∧
    ((-(Aᵀ * A - Bᵀ * B)).PosDef →
      A = (A * pinv B) * B ∧ (1 - (A * pinv B)ᵀ * (A * pinv B)).PosDef) := by sorry
end QuadMatIneq.Petersen
