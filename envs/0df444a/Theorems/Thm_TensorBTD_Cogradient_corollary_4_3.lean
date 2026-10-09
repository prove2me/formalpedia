-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_corollary_4_3
-- name    : TensorBTD.Cogradient.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:56.917687+00:00
-- url     : https://prove2.me/theorems/bcce5838-b468-421f-8ba1-2068149981ce
-- title:
--   Corollary 4.3, p. 7 — (V^σ)ᴴV^σ = W^σ
-- statement:
--   Let $A^{(1)},\dots,A^{(N)}$ be complex matrices with $I_n$ rows and a common set of $K$ columns, $N=P+Q$, and let $\sigma$ be any set of modes. With the Khatri–Rao string $V^\sigma=\bigodot_{n\notin\sigma}A^{(n)}$ of (3.2) and
--   $$W^{\sigma}=\mathop{\ast}_{n\notin\sigma}A^{(n)\mathrm H}A^{(n)},$$
--   the Hadamard product of the Gramians of the factor matrices outside $\sigma$,
--   $$(V^{\sigma})^{\mathrm H}V^{\sigma}=W^{\sigma}.$$
--
--   In the proof of Theorem 4.4 it is applied with $\sigma=\{n\}$, to compute $\partial f^{(1)}/\partial A^{(n)}=\overline{A}^{(n)}W^{\{n\}}$.
--
--   **Formalization Note.** Modes are `Fin P ⊕ Fin Q`; the rows of $V^\sigma$ are indexed by the tuple of indices of the modes outside $\sigma$. The column set is an arbitrary finite type (in the mission it is the $R'$ columns of the CPD).
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 7, Corollary 4.3; (3.2), p. 4

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Corollary 4.3, p. 7: `(V^σ)ᴴ V^σ = W^σ` for every set `σ` of modes and all factor matrices
with a common finite column set `K`. -/
theorem corollary_4_3 {P Q : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {K : Type*} [Fintype K]
    (σ : Finset (Fin P ⊕ Fin Q)) (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) K ℂ) :
    (V σ A)ᴴ * V σ A = W σ A := by sorry

end TensorBTD.Cogradient
