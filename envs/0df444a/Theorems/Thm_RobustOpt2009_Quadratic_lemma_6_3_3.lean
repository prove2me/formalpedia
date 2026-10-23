-- Prove2me | Theorems.Thm_RobustOpt2009_Quadratic_lemma_6_3_3
-- name    : RobustOpt2009.Quadratic.lemma_6_3_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:50.676648+00:00
-- url     : https://prove2.me/theorems/5d2757f7-4133-470d-85db-39a6b678b19c
-- title:
--   Lemma 6.3.3 — semidefinite representation of the Lorentz cone
-- statement:
--   For every $y\in\mathbb R^k$ and $t\in\mathbb R$,
--   $$\|y\|_2\le t\quad\Longleftrightarrow\quad\begin{pmatrix}t&y^T\\y&tI_k\end{pmatrix}\succeq0.$$
--   This identifies Lorentz-cone membership with an explicit positive-semidefinite matrix constraint.
--
--   **Formalization Note** The scalar coordinate is first. The statement includes $t=0$ and negative $t$; dimension zero yields the scalar condition $0\le t$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Lemma 6.3.3, printed p. 163 (PDF p. 189).

import Mathlib
import Definitions.Def_RobustOpt2009_Quadratic_Setup

namespace RobustOpt2009.Quadratic

/-- Lemma 6.3.3, printed p. 163: the full Lorentz/arrow equivalence, including t = 0. -/
theorem lemma_6_3_3 {k : ℕ} (y : Fin k → ℝ) (t : ℝ) :
    euclidNorm y ≤ t ↔ (arrow y t).PosSemidef := by sorry

end RobustOpt2009.Quadratic
