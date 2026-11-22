-- Prove2me | Theorems.Thm_SKHessianAscent_lemma_5_5
-- name    : SKHessianAscent.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:15:05.571591+00:00
-- url     : https://prove2.me/theorems/7d89f249-a024-410d-ba4d-9849bc06ce45
-- title:
--   Lemma 5.5 — comparison of the expected GOE block resolvent with the GUE one and with the free limit
-- statement:
--   Let $S$ be a semicircular element free from $(M_n(\mathbb C),\mathrm{tr}_n)$ in $(\mathcal M_n,\tau_n)$ and $\mathbf E_{M_n}$ the trace-preserving conditional expectation onto $M_n(\mathbb C)$. Fix $a\in[0,1]$, $\beta>0$ and a diagonal $W=D^{-1}$ with entries in $[0,1]$. For a Hermitian $n\times n$ matrix $X$ (or $X=S$) and $z\in\mathbb C\setminus\mathbb R$ let
--   $$R_X(z)=\Big[zI_{2n}-\begin{pmatrix}0&I_n+D^{-1}(aI_n-\beta X)\\I_n+(aI_n-\beta X)D^{-1}&0\end{pmatrix}\Big]^{-1}.$$
--   Let $A\sim\mathrm{GOE}(n)$ and $A_{\mathrm{GUE}}\sim\mathrm{GUE}(n)$. Then for $b=\mathrm{Im}\,z\neq0$,
--   $$\big\|\mathbf E\,R_A(z)-\mathbf E\,R_{A_{\mathrm{GUE}}}(z)\big\|_{\mathrm{op}}\le\frac{2\beta^2}{n|b|^3},\tag{5.27}$$
--   $$\big\|\mathbf E\,R_{A_{\mathrm{GUE}}}(z)-(\mathrm{id}_2\otimes\mathbf E_{M_n})\big[R_S(z)\big]\big\|_{\mathrm{op}}\le\frac{2\beta^4}{n|b|^5}.\tag{5.28}$$
--
--   **Formalization Note** The paper writes $R_t(z)$ for the interpolation $A_t=\sqrt tA+\sqrt{1-t}A_{\mathrm{GUE}}$; only $t=1$ (GOE) and $t=0$ (GUE) enter the statement, through expectations, so the two matrices need not be coupled. $(\mathrm{id}_2\otimes\mathbf E_{M_n})[R_S(z)]$ is the published matrix-valued Stieltjes transform `Pencil.stieltjes` of the block pencil.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §5.3, Lemma 5.5, (5.27)–(5.28), pp. 31–32

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal
import Definitions.Def_SKHessianAscent_FreeModel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace SKHessianAscent

theorem lemma_5_5 (n : ℕ) (β a : ℝ) (w : Fin n → ℝ) (hβ : 0 < β) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (z : ℂ) (hz : z.im ≠ 0)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : GueIdx n → H →L[ℂ] H) (ω : H) (hs : FreeWeaver.Walk.IsStdFreeSemicircular s ω) :
    let R : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
      fun A => (z • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) - cBlock β a w A)⁻¹
    let ER1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
      fun k l => ∫ A, R (Matrix.of fun i j => ((A i j : ℝ) : ℂ)) k l ∂(RandMatDisc.goe n)
    let ER0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
      fun k l => ∫ A, R (Matrix.of A) k l ∂(gue n)
    FreeWeaver.Walk.opNorm (ER1 - ER0) ≤ 2 * β ^ 2 / (n * |z.im| ^ 3) ∧
    FreeWeaver.Walk.opNorm (ER0 - (blockPencil β a w).stieltjes s ω z) ≤
      2 * β ^ 4 / (n * |z.im| ^ 5) := by sorry

end SKHessianAscent
