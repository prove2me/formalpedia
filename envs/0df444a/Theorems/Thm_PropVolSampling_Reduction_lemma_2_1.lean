-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_lemma_2_1
-- name    : PropVolSampling.Reduction.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:22.313503+00:00
-- url     : https://prove2.me/theorems/63dcee72-a0d5-45a9-9e67-d868ee57691b
-- title:
--   Lemma 2.1, p. 7 — $\det(V_T(x)^\top V_T(x)) = x^T\det(V_T^\top V_T)$
-- statement:
--   Let $V=[v_1,\dots,v_n]$ be a real $d\times n$ matrix and $x\in\mathbb R^n$ with $x_i\ge 0$ for all $i$. For $T\subseteq[n]$ write $V_T$ for the $d\times|T|$ submatrix of columns $v_i$, $i\in T$, and $V_T(x)$ for the matrix with columns $\sqrt{x_i}\,v_i$, $i\in T$. If $|T|\le d$, then
--   $$\det\big(V_T(x)^\top V_T(x)\big)=x^T\det\big(V_T^\top V_T\big),\qquad x^T=\prod_{i\in T}x_i.$$
--
--   It converts the $x$-weighted Cauchy–Binet sums of the relaxation's matrix into unweighted Gram determinants times monomials $x^T$, which is what makes them comparable with the sampling probabilities.
--
--   **Formalization Note** The page takes $x\in\mathbb R^n_+$ (Algorithm 1, step 2); nonnegativity is stated as a hypothesis so that $\sqrt{x_i}^2=x_i$.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 7, Lemma 2.1

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem lemma_2_1 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (T : Finset (Fin n)) (hT : T.card ≤ d) :
    ((colSubW V x T)ᵀ * colSubW V x T).det = xPow x T * ((colSub V T)ᵀ * colSub V T).det := by sorry

end PropVolSampling.Reduction
