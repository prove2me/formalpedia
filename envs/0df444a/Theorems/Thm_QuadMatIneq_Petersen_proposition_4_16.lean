-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_proposition_4_16
-- name    : QuadMatIneq.Petersen.proposition_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:55.467044+00:00
-- url     : https://prove2.me/theorems/5cbd3e8a-326d-4d04-8bff-ab08f2226e8e
-- title:
--   Proposition 4.16 (Petersen's lemma), p. 17 — robust strict and non-strict LMIs over $F^\top F\leqslant\bar F$ iff $C+\lambda EE^\top+\lambda^{-1}G^\top\bar FG<0$ ($\leqslant0$) for some $\lambda>0$
-- statement:
--   Let $C\in\mathbb R^{n\times n}$, $E\in\mathbb R^{n\times p}$, $\bar F\in\mathbb R^{q\times q}$ and $G\in\mathbb R^{q\times n}$ with $C=C^\top$ and $\bar F\geqslant0$, and define the uncertainty set
--   $$\mathcal F:=\{F\in\mathbb R^{p\times q}\mid F^\top F\leqslant\bar F\}.$$
--
--   **(a)** The following are equivalent:
--
--   - (4.15a) $C+EFG+G^\top F^\top E^\top<0$ for all $F\in\mathcal F$;
--   - (4.15b) there exists $\lambda>0$ such that $C+\lambda EE^\top+\lambda^{-1}G^\top\bar FG<0$.
--
--   **(b)** Suppose that $E\neq0$, $\bar F>0$ and $G\neq0$. Then the following are equivalent:
--
--   - (4.16a) $C+EFG+G^\top F^\top E^\top\leqslant0$ for all $F\in\mathcal F$;
--   - (4.16b) there exists $\lambda>0$ such that $C+\lambda EE^\top+\lambda^{-1}G^\top\bar FG\leqslant0$.
--
--   In display form, part (a) reads
--   $$\big(\forall F\in\mathcal F:\ C+EFG+G^\top F^\top E^\top<0\big)\iff\exists\,\lambda>0:\ C+\lambda EE^\top+\lambda^{-1}G^\top\bar FG<0 .$$
--
--   Petersen's lemma removes the uncertainty $F$ from a robust linear matrix inequality at the price of one scalar multiplier $\lambda$; it is a standard tool in robust and data-driven control. The paper recovers both forms from its matrix S-lemmas.
--
--   **Formalization Note** $X<0$ is `(−X).PosDef` and $X\leqslant0$ is `(−X).PosSemidef`, both including symmetry; $F^\top F\leqslant\bar F$ is `(F̄ − FᵀF).PosSemidef`. The multiplier is called `lam`, required positive, so $\lambda^{-1}$ is the true inverse. The hypotheses $E\neq0$, $\bar F>0$, $G\neq0$ are attached to part (b) only, as on the page.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Proposition 4.16 (Petersen's lemma), p. 17

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

namespace QuadMatIneq.Petersen
open Matrix
theorem proposition_4_16 {n p q : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (E : Matrix (Fin n) (Fin p) ℝ) (Fbar : Matrix (Fin q) (Fin q) ℝ)
    (G : Matrix (Fin q) (Fin n) ℝ) (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef) :
    ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
        (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosDef) ↔
      ∃ lam : ℝ, 0 < lam ∧ (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosDef) ∧
    (E ≠ 0 → Fbar.PosDef → G ≠ 0 →
      ((∀ F ∈ (uncSet Fbar : Set (Matrix (Fin p) (Fin q) ℝ)),
          (-(C + E * F * G + Gᵀ * Fᵀ * Eᵀ)).PosSemidef) ↔
        ∃ lam : ℝ, 0 < lam ∧
          (-(C + lam • (E * Eᵀ) + lam⁻¹ • (Gᵀ * Fbar * G))).PosSemidef)) := by sorry
end QuadMatIneq.Petersen
