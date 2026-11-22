-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_5_1
-- name    : SKHessianAscent.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:12:20.865711+00:00
-- url     : https://prove2.me/theorems/940a1279-4265-4620-88dc-c7ed61808651
-- title:
--   Lemma 5.1 — derivative bounds for the cubed positive part $Z\mapsto Z_+^3$ on symmetric matrices
-- statement:
--   The matrix map $Z\mapsto Z_+^3$ (the function $z\mapsto z_+^3$ applied to the eigenvalues of a symmetric matrix $Z$) is twice continuously Fréchet differentiable on $\mathrm{Sym}_n(\mathbb R)$. For every symmetric $Z$ with $\|Z\|_{\mathrm{op}}\le1$, symmetric directions $H,K$, and $p\in\{2,\infty\}$,
--
--   $$
--   \big\|d(Z_+^3)[H]\big\|_{L^p}\le4\|H\|_{L^p},\qquad\big\|d^2(Z_+^3)[H,K]\big\|_{L^2}\le10\,\|H\|_{L^2}\|K\|_{\mathrm{op}},
--   $$
--
--   where $\|\cdot\|_{L^2}$ is the normalized Schatten 2-norm and $\|\cdot\|_{L^\infty}=\|\cdot\|_{\mathrm{op}}$.
--
--   The constants do not depend on the dimension; the lemma is the source of the dimension-free derivative bounds for the cutoff $\phi$.
--
--   **Formalization Note** Differentiability on $\mathrm{Sym}_n(\mathbb R)$ is stated for $g=(Z\mapsto Z_+^3)\circ\mathrm{symPart}$ on all matrices, and $d(Z_+^3)[H]$, $d^2(Z_+^3)[H,K]$ are the first and second Fréchet derivatives of $g$ at symmetric $Z$ in symmetric directions. The space of matrices carries the operator norm; in finite dimension the notion of differentiability does not depend on this choice.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Lemma 5.1, eq. (5.3), p. 25

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
open scoped Matrix.Norms.L2Operator

namespace SKHessianAscent

theorem lemma_5_1 (n : ℕ) :
    let g : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
      fun X => matFun cubePos (symPart X)
    ContDiff ℝ 2 g ∧
      ∀ Z H K : Matrix (Fin n) (Fin n) ℝ, Z.IsSymm → H.IsSymm → K.IsSymm → opNorm Z ≤ 1 →
        schatten2 (fderiv ℝ g Z H) ≤ 4 * schatten2 H ∧
        opNorm (fderiv ℝ g Z H) ≤ 4 * opNorm H ∧
        schatten2 (fderiv ℝ (fderiv ℝ g) Z H K) ≤ 10 * schatten2 H * opNorm K := by sorry

end SKHessianAscent
