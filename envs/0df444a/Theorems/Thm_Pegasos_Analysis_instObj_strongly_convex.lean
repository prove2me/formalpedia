-- Prove2me | Theorems.Thm_Pegasos_Analysis_instObj_strongly_convex
-- name    : Pegasos.Analysis.instObj_strongly_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:02.651019+00:00
-- url     : https://prove2.me/theorems/64c590b9-accf-4767-b078-1bdb2cad67f5
-- title:
--   Proof of Theorem 1 — the mini-batch objective f(·; A) is λ-strongly convex
-- statement:
--   For any data $(x_i, y_i)_{i\in[m]}$ and any mini-batch $A$ of $k$ indices, the instantaneous objective $f(w;A) = \frac\lambda2\|w\|^2 + \frac1k\sum_{i\in A}\max\{0,1-y_i\langle w,x_i\rangle\}$ is $\lambda$-strongly convex in the paper's sense:
--   $$w \;\mapsto\; f(w;A) - \frac\lambda2\|w\|^2 \quad\text{is convex on } \mathbb R^n.$$
--
--   This verifies the first hypothesis of Lemma 1 for the functions $f_t = f(\cdot;A_t)$.
--
--   **Formalization Note.** The paper's definition of $\lambda$-strong convexity (p. 9) is used verbatim, so the statement is the convexity of the averaged hinge loss over the batch; it holds for every real $\lambda$ and every $k$ (at $k = 0$, Lean's $1/0 = 0$ makes the average $0$).
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 11, proof of Theorem 1

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Proof of Theorem 1** (p. 11): the instantaneous objective `f(·; A)` of Eq. (7) is
λ-strongly convex in the paper's sense (p. 9): `f(w; A) − λ/2‖w‖²` is a convex function
of `w`. -/
theorem instObj_strongly_convex {n m k : ℕ} (lam : ℝ)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (B : Fin k → Fin m) :
    ConvexOn ℝ Set.univ (fun w => instObj lam x y B w - lam / 2 * ‖w‖ ^ 2) := by sorry

end Pegasos.Analysis
