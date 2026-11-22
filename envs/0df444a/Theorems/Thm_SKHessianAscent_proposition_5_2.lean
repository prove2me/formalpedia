-- Prove2me | Theorems.Thm_SKHessianAscent_proposition_5_2
-- name    : SKHessianAscent.proposition_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-22T20:13:10.413305+00:00
-- url     : https://prove2.me/theorems/34b819cd-84cd-492f-b866-4c82d785f6f7
-- title:
--   Proposition 5.2 — regularity and block identities for the reciprocal extension $\phi$ and the functional $\Phi_{a,W,T}$
-- statement:
--   Let $\gamma_Y>0$, $\phi(y)=\big[y+\gamma_Y\big(\tfrac{(\gamma_Y-y)_+}{\gamma_Y+y}\big)^3\big]^{-1}$, and for $\beta>0$, $a\in[0,1]$, symmetric $A$, $W\in\mathcal D_n([0,1])$, $T\in\mathcal D_n(\mathbb R)$ let $M=aI_n-\beta A$ and $\Phi_{a,W,T}(A)=\mathrm{tr}_n[T\phi((I_n+WM)(I_n+MW))]$. All constants are independent of the dimension.
--
--   1. **Cutoff bounds.** $\phi$ is well defined and positive on $(-\gamma_Y,\infty)$. For $y\ge0$, $\phi(y)^{-1}\ge y$ and $\phi(y)^{-1}\ge(\sqrt6-2)\gamma_Y\ge4\gamma_Y/9$. Also $\phi(y)=y^{-1}$ for $y\ge\gamma_Y$. For every symmetric $Z$,
--   $$\|\phi(Z^2)\|_{\mathrm{op}}\le\frac{9}{4\gamma_Y},\qquad\|Z\phi(Z^2)^{1/2}\|_{\mathrm{op}}\le1.$$
--   2. **Regularity.** The map $Z\mapsto\phi(Z^2)$ is twice continuously Fréchet differentiable on $\mathrm{Sym}_n(\mathbb R)$, and there is a universal $C>0$ such that for all symmetric $Z,\widetilde Z,H,K$ and $p\in\{2,\infty\}$:
--   $$\|d[\phi(Z^2)][H]\|_{L^p}\le C\gamma_Y^{-3/2}\|H\|_{L^p},\qquad\|d^2[\phi(Z^2)][H,K]\|_{L^2}\le C\gamma_Y^{-2}\|H\|_{L^2}\|K\|_{\mathrm{op}},$$
--   $$\big\|\big(d[\phi(Z^2)]-d[\phi(\widetilde Z^2)]\big)[H]\big\|_{L^2}\le C\gamma_Y^{-2}\|Z-\widetilde Z\|_{\mathrm{op}}\|H\|_{L^2}.$$
--   3. **Block representation.**
--   $$\Phi_{a,W,T}(A)=\mathrm{tr}_{2n}\Big[\begin{pmatrix}2T&0\\0&0\end{pmatrix}\phi\Big(\begin{pmatrix}0&I_n+WM\\I_n+MW&0\end{pmatrix}^2\Big)\Big],$$
--   and for every symmetric $H$: $\big\|\begin{pmatrix}2T&0\\0&0\end{pmatrix}\big\|_{L^2}=\sqrt2\|T\|_{L^2}$ and $\big\|\begin{pmatrix}0&WH\\HW&0\end{pmatrix}\big\|_{L^2}=\|WH\|_{L^2}\le\|H\|_{L^2}$.
--   4. **Affine dependence on $A$.** For every symmetric $H$, $d_A\Big[\begin{pmatrix}0&I_n+WM\\I_n+MW&0\end{pmatrix}\Big][H]=-\beta\begin{pmatrix}0&WH\\HW&0\end{pmatrix}$, of normalized Schatten 2-norm at most $\beta\|H\|_{L^2}$.
--   5. **Agreement on the safe set.** For $W\succ0$ and $D=W^{-1}$: if $(I_n+WM)(I_n+MW)\succeq\gamma_YI_n$ then $\phi((I_n+WM)(I_n+MW))=((I_n+WM)(I_n+MW))^{-1}=D(M+D)^{-2}D$.
--
--   The proposition collects what is needed to run the chaining and interpolation arguments on the regularized functional and to return to the original quantity on the safe set.
--
--   **Formalization Note** The universal constant $C$ of part 2 is quantified before $n$ and $\gamma_Y$. Part 2 is stated for $Z\mapsto\phi(\mathrm{symPart}(Z)^2)$ on all matrices (see `SKHessianAscent_Reciprocal`). In part 4 the block matrix is affine in $A$, and the derivative is stated as the exact identity $B(A+H)=B(A)-\beta\begin{pmatrix}0&WH\\HW&0\end{pmatrix}$. $\phi(Z^2)^{1/2}$ is the matrix function $\sqrt{\phi}$ of $Z^2$. Block matrices are indexed by `Fin n ⊕ Fin n` and $\mathrm{tr}_{2n}=\mathrm{Tr}/(2n)$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Proposition 5.2, eqs. (5.7)–(5.13), p. 26

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_SKHessianAscent_Model
import Definitions.Def_SKHessianAscent_Reciprocal

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
open scoped Matrix.Norms.L2Operator

namespace SKHessianAscent

theorem proposition_5_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (γ : ℝ), 0 < γ →
        -- (a) cutoff bounds
        ((∀ y : ℝ, -γ < y → 0 < phi γ y) ∧
          (∀ y : ℝ, 0 ≤ y → y ≤ (phi γ y)⁻¹ ∧ (Real.sqrt 6 - 2) * γ ≤ (phi γ y)⁻¹) ∧
          4 * γ / 9 ≤ (Real.sqrt 6 - 2) * γ ∧
          (∀ y : ℝ, γ ≤ y → phi γ y = y⁻¹) ∧
          ∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.IsSymm →
            opNorm (matFun (phi γ) (Z ^ 2)) ≤ 9 / (4 * γ) ∧
            opNorm (Z * matFun (fun y => Real.sqrt (phi γ y)) (Z ^ 2)) ≤ 1) ∧
        -- (b) regularity of the squared-argument cutoff
        (
          let g : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
            fun X => matFun (phi γ) (symPart X ^ 2)
          ContDiff ℝ 2 g ∧
          ∀ Z Z' H K : Matrix (Fin n) (Fin n) ℝ, Z.IsSymm → Z'.IsSymm → H.IsSymm → K.IsSymm →
            schatten2 (fderiv ℝ g Z H) ≤ C * γ ^ (-(3 : ℝ) / 2) * schatten2 H ∧
            opNorm (fderiv ℝ g Z H) ≤ C * γ ^ (-(3 : ℝ) / 2) * opNorm H ∧
            schatten2 (fderiv ℝ (fderiv ℝ g) Z H K) ≤ C * γ ^ (-2 : ℤ) * schatten2 H * opNorm K ∧
            schatten2 ((fderiv ℝ g Z - fderiv ℝ g Z') H) ≤
              C * γ ^ (-2 : ℤ) * opNorm (Z - Z') * schatten2 H) ∧
        ∀ (β a : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (w τ : Fin n → ℝ),
          0 < β → 0 ≤ a → a ≤ 1 → A.IsSymm → (∀ i, 0 ≤ w i ∧ w i ≤ 1) →
          -- (c) block representation and normalization
          (PhiFun β γ a w τ A =
              (Matrix.fromBlocks ((2 : ℝ) • Matrix.diagonal τ) 0 0 0 *
                matFun (phi γ) (blockArg β a w A ^ 2)).trace / (2 * n) ∧
            schatten2Block (Matrix.fromBlocks ((2 : ℝ) • Matrix.diagonal τ) 0 0 0) =
              Real.sqrt 2 * schatten2 (Matrix.diagonal τ) ∧
            ∀ H : Matrix (Fin n) (Fin n) ℝ, H.IsSymm →
              schatten2Block (Matrix.fromBlocks 0 (Matrix.diagonal w * H) (H * Matrix.diagonal w) 0) =
                schatten2 (Matrix.diagonal w * H) ∧
              schatten2 (Matrix.diagonal w * H) ≤ schatten2 H) ∧
          -- (d) affine dependence on A
          (∀ H : Matrix (Fin n) (Fin n) ℝ, H.IsSymm →
            blockArg β a w (A + H) = blockArg β a w A -
              β • Matrix.fromBlocks 0 (Matrix.diagonal w * H) (H * Matrix.diagonal w) 0 ∧
            schatten2Block
                (β • Matrix.fromBlocks 0 (Matrix.diagonal w * H) (H * Matrix.diagonal w) 0) ≤
              β * schatten2 H) ∧
          -- (e) agreement on the safe set
          ((∀ i, 0 < w i) →
            (reciprocalArg β a w A - γ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
              matFun (phi γ) (reciprocalArg β a w A) = (reciprocalArg β a w A)⁻¹ ∧
              (reciprocalArg β a w A)⁻¹ =
                Matrix.diagonal (fun i => (w i)⁻¹) *
                  ((a • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A +
                    Matrix.diagonal (fun i => (w i)⁻¹))⁻¹) ^ 2 *
                  Matrix.diagonal (fun i => (w i)⁻¹)) := by sorry

end SKHessianAscent
