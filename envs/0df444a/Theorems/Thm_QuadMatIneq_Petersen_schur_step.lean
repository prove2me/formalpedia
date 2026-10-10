-- Prove2me | Theorems.Thm_QuadMatIneq_Petersen_schur_step
-- name    : QuadMatIneq.Petersen.schur_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:48.516282+00:00
-- url     : https://prove2.me/theorems/493a63f7-307e-4d7a-a0f6-27d21f155f82
-- title:
--   Proof of Proposition 4.16, p. 17 — for $\alpha>0$, $M-\alpha N>0$ iff $-C-\alpha G^\top\bar FG-\frac1\alpha EE^\top>0$ (and the $\geqslant$ analogue)
-- statement:
--   Let $C\in\mathbb R^{n\times n}$ be symmetric, $E\in\mathbb R^{n\times p}$, $\bar F\in\mathbb R^{q\times q}$ with $\bar F\geqslant0$, $G\in\mathbb R^{q\times n}$, and let $M,N$ be the matrices (4.17). For every real $\alpha>0$,
--   $$M-\alpha N>0\iff -C-\alpha G^\top\bar FG-\tfrac1\alpha EE^\top>0,$$
--   and
--   $$M-\alpha N\geqslant0\iff -C-\alpha G^\top\bar FG-\tfrac1\alpha EE^\top\geqslant0.$$
--
--   This is the Schur-complement step of the paper's proof: it turns the multiplier condition of the matrix S-lemmas into the condition of Petersen's lemma with $\lambda:=1/\alpha$.
--
--   **Formalization Note** The second (non-strict) equivalence is the analogue the paper uses when it says "the proof of statement (b) is analogous"; it is added to the same item and cited to the same page.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.5.3, proof of Proposition 4.16(a), p. 17 ("By using a Schur complement argument …"); non-strict analogue: proof of (b), same page

import Mathlib
import Definitions.Def_QuadMatIneq_Petersen_QMI
import Definitions.Def_QuadMatIneq_Petersen_Setup

namespace QuadMatIneq.Petersen
open Matrix
theorem schur_step {n p q : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin p) ℝ)
    (Fbar : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin q) (Fin n) ℝ)
    (hC : C.IsHermitian) (hFbar : Fbar.PosSemidef) (α : ℝ) (hα : 0 < α) :
    ((petersenM C E - α • petersenN Fbar G).PosDef ↔
      (-C - α • (Gᵀ * Fbar * G) - α⁻¹ • (E * Eᵀ)).PosDef) ∧
    ((petersenM C E - α • petersenN Fbar G).PosSemidef ↔
      (-C - α • (Gᵀ * Fbar * G) - α⁻¹ • (E * Eᵀ)).PosSemidef) := by sorry
end QuadMatIneq.Petersen
