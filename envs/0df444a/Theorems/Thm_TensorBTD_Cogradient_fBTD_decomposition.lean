-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_fBTD_decomposition
-- name    : TensorBTD.Cogradient.fBTD_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:21.894293+00:00
-- url     : https://prove2.me/theorems/cc8a9376-aecc-4c28-8d3f-d210e77a78f7
-- title:
--   Proof of Theorem 4.4, p. 8 — f_BTD = ½(f^(1) − f^(2) − f̄^(2) + f^(3)) for every mode n
-- statement:
--   Let $\mathcal T$ be an $N$th-order tensor, $N=P+Q$. First, $f_{\mathrm{BTD}}$ is the objective of the unstructured CPD evaluated at the structured factor matrices (3.6): for all unknowns $z$,
--   $$f_{\mathrm{BTD}}(z)=\tfrac12\Big\|\sum_{r'}a^{(1)}_{r'}\circ\cdots\circ a^{(N)}_{r'}-\mathcal T\Big\|^2\quad\text{with } A^{(P+q)}=C^{(q)}E .$$
--   Second, for all factor matrices $A^{(1)},\dots,A^{(N)}\in\mathbb C^{I_n\times R'}$ of the unstructured CPD and every mode $n$, with
--   $$f^{(1)}=\|A^{(n)}V^{\{n\}\mathrm T}\|^2,\qquad f^{(2)}=\langle T_{(n)},A^{(n)}V^{\{n\}\mathrm T}\rangle,\qquad f^{(3)}=\|T_{(n)}\|^2,$$
--   one has
--   $$f=\tfrac12\big(f^{(1)}-f^{(2)}-\overline{f^{(2)}}+f^{(3)}\big),$$
--   where $f=\frac12\|\mathcal F\|^2$ is the objective of the unstructured CPD.
--
--   This splits the objective into a part depending only on the factors, a part linear in the data, and a constant; it opens the proof of Theorem 4.4.
--
--   **Formalization Note.** The inner product is Definition 2.1's, conjugate on the first argument. The identity holds for every mode $n$ simultaneously, because the mode-$n$ unfolding of the residual is $A^{(n)}V^{\{n\}\mathrm T}-T_{(n)}$ (3.8). All quantities are cast to $\mathbb C$.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 8, proof of Theorem 4.4, first sentence; (3.6)–(3.8), p. 6

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Proof of Theorem 4.4, p. 8, first sentence: `f_BTD` is the objective of the unstructured CPD
at the factor matrices `A^(n)` of (3.6), and for every mode `n`,
`f = ½ (f^(1) − f^(2) − conj f^(2) + f^(3))` with `f^(1) = ‖A^(n) V^{n}ᵀ‖²`,
`f^(2) = ⟨T_(n), A^(n) V^{n}ᵀ⟩`, `f^(3) = ‖T_(n)‖²`. -/
theorem fBTD_decomposition {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I) :
    (∀ z : TensorBTD.Gramian.Unk I L → ℂ, fBTD T z = fCPD T (TensorBTD.Gramian.fullVec z)) ∧
    ∀ (x : TensorBTD.Gramian.GIdx I L → ℂ) (n : Fin P ⊕ Fin Q),
      fCPD T x = (1 / 2 : ℂ) *
        (fOne n x - fTwo T n x - starRingEnd ℂ (fTwo T n x) + fThree T n) := by sorry

end TensorBTD.Cogradient
