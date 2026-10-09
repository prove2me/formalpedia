-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_cograd_f2_f3
-- name    : TensorBTD.Cogradient.cograd_f2_f3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:15.151141+00:00
-- url     : https://prove2.me/theorems/6fbaca9c-97ce-426f-8cf0-aa18c9ad090d
-- title:
--   Proof of Theorem 4.4, p. 8 — ∂f^(2)/∂A^(n) = T̄_(n)·V^{n} and ∂f̄^(2)/∂A^(n) = ∂f^(3)/∂A^(n) = 0
-- statement:
--   Consider the unstructured CPD with factor matrices $A^{(1)},\dots,A^{(N)}\in\mathbb C^{I_n\times R'}$, a tensor $\mathcal T$ and a mode $n$. Let
--   $$f^{(2)}=\langle T_{(n)},A^{(n)}V^{\{n\}\mathrm T}\rangle,\qquad f^{(3)}=\|T_{(n)}\|^2 .$$
--   Then, for the cogradients with respect to the entries of $A^{(n)}$,
--   1. $\dfrac{\partial f^{(2)}}{\partial A^{(n)}}=\overline{T}_{(n)}\cdot V^{\{n\}}$, where $\overline{T}_{(n)}$ is the entrywise conjugate of the mode-$n$ unfolding;
--   2. $\dfrac{\partial \overline{f^{(2)}}}{\partial A^{(n)}}=0$;
--   3. $\dfrac{\partial f^{(3)}}{\partial A^{(n)}}=0$.
--
--   Together with $\partial f^{(1)}/\partial A^{(n)}=\overline{A}^{(n)}W^{\{n\}}$ and the decomposition $f=\frac12(f^{(1)}-f^{(2)}-\overline{f^{(2)}}+f^{(3)})$ this gives (4.5a).
--
--   **Formalization Note.** The inner product is conjugate on the first argument (Definition 2.1), so $f^{(2)}$ is holomorphic in $A^{(n)}$ and $\overline{f^{(2)}}$ is antiholomorphic. The mode $n$ may be any of the $N$ modes.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 8, proof of Theorem 4.4, sentence after the first display

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Proof of Theorem 4.4, p. 8: for every mode `n` of the unstructured CPD,
`∂f^(2)/∂A^(n) = T̄_(n) · V^{n}` and `∂ conj(f^(2))/∂A^(n) = ∂f^(3)/∂A^(n) = 0`. -/
theorem cograd_f2_f3 {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (x : TensorBTD.Gramian.GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) :
    cogradMatG (fTwo T n) x n = (unfolding T n).map (starRingEnd ℂ) * V {n} (TensorBTD.Gramian.cpdFactor x) ∧
    cogradMatG (fun y => starRingEnd ℂ (fTwo T n y)) x n = 0 ∧
    cogradMatG (fun _ : TensorBTD.Gramian.GIdx I L → ℂ => fThree T n) x n = 0 := by sorry

end TensorBTD.Cogradient
