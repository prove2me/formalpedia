-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_theorem_4_4
-- name    : TensorBTD.Cogradient.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:57.636737+00:00
-- url     : https://prove2.me/theorems/cee330e3-c6b6-446c-9982-b3f2621ddc7a
-- title:
--   Theorem 4.4, p. 8 — 2∂f/∂A^(p) = Ā^(p)W^{p} − T̄_(p)V^{p}, 2∂f/∂C^(q) = C̄^(q)EW^{P+q}Eᵀ − T̄_(P+q)V^{P+q}Eᵀ
-- statement:
--   Let $\mathcal T\in\mathbb C^{I_1\times\cdots\times I_N}$ with $N=P+Q$, and let
--   $$z=(\operatorname{vec}A^{(1)},\dots,\operatorname{vec}A^{(P)},\operatorname{vec}C^{(1)},\dots,\operatorname{vec}C^{(Q)})$$
--   be the vector of unknowns of the (rank-$L_r\circ$ rank-1) BTD, with factor matrices $A^{(1)},\dots,A^{(P)}$ and $A^{(P+q)}=C^{(q)}E$ (3.6). Let $f_{\mathrm{BTD}}=\frac12\|\mathcal F_{\mathrm{BTD}}\|^2$ be the objective (3.7). Then the complex cogradient $\partial f_{\mathrm{BTD}}/\partial z$ is
--   $$\frac{\partial f_{\mathrm{BTD}}}{\partial z}=\Big(\operatorname{vec}\frac{\partial f_{\mathrm{BTD}}}{\partial A^{(1)}},\dots,\operatorname{vec}\frac{\partial f_{\mathrm{BTD}}}{\partial A^{(P)}},\operatorname{vec}\frac{\partial f_{\mathrm{BTD}}}{\partial C^{(1)}},\dots,\operatorname{vec}\frac{\partial f_{\mathrm{BTD}}}{\partial C^{(Q)}}\Big)\qquad(4.4)$$
--   where, for $1\le p\le P$ and $1\le q\le Q$,
--   $$2\,\frac{\partial f_{\mathrm{BTD}}}{\partial A^{(p)}}=\overline{A}^{(p)}\cdot W^{\{p\}}-\overline{T}_{(p)}\cdot V^{\{p\}},\qquad(4.5a)$$
--   $$2\,\frac{\partial f_{\mathrm{BTD}}}{\partial C^{(q)}}=\overline{C}^{(q)}\cdot E\cdot W^{\{P+q\}}\cdot E^{\mathrm T}-\overline{T}_{(P+q)}\cdot V^{\{P+q\}}\cdot E^{\mathrm T}.\qquad(4.5b)$$
--   Here overbars denote entrywise complex conjugation, $T_{(n)}$ is the mode-$n$ unfolding, and $V^{\{n\}}$, $W^{\{n\}}$ are the Khatri–Rao string and the Hadamard product of Gramians of all factor matrices except the $n$-th, computed from the structured factor matrices.
--
--   The cogradient is what complex quasi-Newton and nonlinear conjugate gradient methods need at every iteration; the formula evaluates it with small $R'\times R'$ Gramians and one tensor–Khatri–Rao product per mode.
--
--   **Formalization Note.** The cogradient is the Wirtinger derivative $\frac12(\partial_x-\mathrm i\,\partial_y)$ taken coordinatewise; the matrices $\partial f/\partial A^{(p)}$ and $\partial f/\partial C^{(q)}$ are built entry by entry from it, so (4.4) holds by construction and the statement consists of (4.5a) and (4.5b). Indices are 0-based, modes are `Fin P ⊕ Fin Q`, and `vec` is column-major. No hypotheses are placed on $\mathcal T$, the factor matrices, $P$, $Q$, $R$ or the $L_r$.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 8, Theorem 4.4, (4.4)–(4.5b)

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Theorem 4.4, p. 8, (4.5a)–(4.5b): the cogradient of `f_BTD` with respect to the unknowns
`A^(p)` and `C^(q)` is
`2 ∂f/∂A^(p) = Ā^(p) W^{p} − T̄_(p) V^{p}` and
`2 ∂f/∂C^(q) = C̄^(q) E W^{P+q} Eᵀ − T̄_(P+q) V^{P+q} Eᵀ`, where `V` and `W` are built from
the structured factor matrices `A^(n)` of (3.6). -/
theorem theorem_4_4 {P Q R : ℕ} (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) (T : TensorBTD.Gramian.Tensor I)
    (z : TensorBTD.Gramian.Unk I L → ℂ) :
    (∀ p : Fin P, (2 : ℂ) • cogradA (fBTD T) z p =
        (Amat z p).map (starRingEnd ℂ) * W {.inl p} (TensorBTD.Gramian.factor z) -
          (unfolding T (.inl p)).map (starRingEnd ℂ) * V {.inl p} (TensorBTD.Gramian.factor z)) ∧
    (∀ q : Fin Q, (2 : ℂ) • cogradC (fBTD T) z q =
        (Cmat z q).map (starRingEnd ℂ) * TensorBTD.Gramian.E L * W {.inr q} (TensorBTD.Gramian.factor z) * (TensorBTD.Gramian.E L)ᵀ -
          (unfolding T (.inr q)).map (starRingEnd ℂ) * V {.inr q} (TensorBTD.Gramian.factor z) * (TensorBTD.Gramian.E L)ᵀ) := by sorry

end TensorBTD.Cogradient
