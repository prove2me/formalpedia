-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_cograd_f1
-- name    : TensorBTD.Cogradient.cograd_f1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:17.81461+00:00
-- url     : https://prove2.me/theorems/777b22cd-312a-4a12-926b-fe28ea4aa880
-- title:
--   Proof of Theorem 4.4, p. 8 — ∂f^(1)/∂A^(n) = Ā^(n)·W^{n}
-- statement:
--   Consider the unstructured CPD with factor matrices $A^{(1)},\dots,A^{(N)}\in\mathbb C^{I_n\times R'}$ and fix a mode $n$. Let
--   $$f^{(1)}=\|A^{(n)}V^{\{n\}\mathrm T}\|^2,$$
--   where $V^{\{n\}}$ is the Khatri–Rao string of all factor matrices except $A^{(n)}$. Then the cogradient of $f^{(1)}$ with respect to the entries of $A^{(n)}$ is
--   $$\frac{\partial f^{(1)}}{\partial A^{(n)}}=\overline{A}^{(n)}\cdot W^{\{n\}},$$
--   where $\overline{A}^{(n)}$ is the entrywise complex conjugate of $A^{(n)}$ and $W^{\{n\}}$ is the Hadamard product of the Gramians $A^{(m)\mathrm H}A^{(m)}$, $m\neq n$.
--
--   This is the factor-dependent part of the cogradient of $f_{\mathrm{BTD}}$.
--
--   **Formalization Note.** The cogradient is $\frac12(\partial_x-\mathrm i\,\partial_y)$ coordinatewise, with all other factor matrices held fixed; the mode $n$ may be any of the $N$ modes, including $n>P$, where $A^{(n)}$ is a free matrix of the unstructured CPD.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 8, proof of Theorem 4.4, first display

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Proof of Theorem 4.4, p. 8, first display: for every mode `n` of the unstructured CPD,
`∂f^(1)/∂A^(n) = Ā^(n) · W^{n}` with `f^(1) = ‖A^(n) V^{n}ᵀ‖²`. -/
theorem cograd_f1 {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (x : TensorBTD.Gramian.GIdx I L → ℂ)
    (n : Fin P ⊕ Fin Q) :
    cogradMatG (fOne n) x n = (TensorBTD.Gramian.cpdFactor x n).map (starRingEnd ℂ) * W {n} (TensorBTD.Gramian.cpdFactor x) := by sorry

end TensorBTD.Cogradient
