-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_theorem_4_8
-- name    : QuadMatIneq.Finsler.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:13:38.342986+00:00
-- url     : https://prove2.me/theorems/e92f2ae1-edb6-4f38-b085-4b6d7a42a742
-- title:
--   Theorem 4.8 (Matrix Finsler's lemma), p. 12 — under $\ker\Theta\subseteq\ker M|M_{22}$, $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$ iff $M-\alpha N\geqslant0$ for some $\alpha\geqslant0$
-- statement:
--   Let $M,N\in\mathbb S^{q+r}$ be partitioned as in (4.1), with $M_{11},N_{11}$ of size $q\times q$ and $M_{22},N_{22}$ of size $r\times r$.
--
--   1. If there exists $\alpha\in\mathbb R$ such that $M-\alpha N\geqslant0$, then $\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)$.
--   2. Define
--   $$\Theta:=\begin{bmatrix}I\\ -N_{22}^\dagger N_{21}\end{bmatrix}^\top M\begin{bmatrix}I\\ -N_{22}^\dagger N_{21}\end{bmatrix}.\qquad(4.4)$$
--   Assume that $q\geqslant1$, $M,N\in\boldsymbol\Pi_{q,r}$, $N\,|\,N_{22}=0$ and $\ker\Theta\subseteq\ker(M\,|\,M_{22})$. Then
--   $$\mathcal Z_r^0(N)\subseteq\mathcal Z_r(M)\iff\exists\,\alpha\geqslant0:\ M-\alpha N\geqslant0 .$$
--
--   Here $\mathcal Z_r^0(N)$ is the set of $Z\in\mathbb R^{r\times q}$ with $\begin{bmatrix}I\\ Z\end{bmatrix}^\top N\begin{bmatrix}I\\ Z\end{bmatrix}=0$ and $\mathcal Z_r(M)$ the set with $\begin{bmatrix}I\\ Z\end{bmatrix}^\top M\begin{bmatrix}I\\ Z\end{bmatrix}\geqslant0$. This is a matrix version of Finsler's lemma: it is the counterpart of the matrix S-lemma (Theorem 4.7) for the case where $N\in\boldsymbol\Pi_{q,r}$ has no positive eigenvalue, in which $\mathcal Z_r(N)=\mathcal Z_r^0(N)$ and the Slater condition fails. Example 4.9 shows that the kernel assumption on $\Theta$ cannot be dropped.
--
--   **Formalization Note** The two statements are the two conjuncts of one Lean theorem. Symmetry of $M$ and $N$ is a hypothesis of both. In the second statement $q\geqslant1$ (`Nonempty ι`) is added: the paper's proof picks a nonzero $\eta\in\mathbb R^q$, and at $q=0$ the equivalence fails ($r=1$, $N=[0]$, $M=[-1]$: every hypothesis holds, both sets are the single point of $\mathbb R^{1\times0}$, and no $\alpha\geqslant0$ gives $M-\alpha N\geqslant0$). The multiplier is any real number in the first statement and nonnegative in the second, as printed. The kernel inclusion is stated with matrix–vector products.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 4.8 (Matrix Finsler's lemma), p. 12, with (4.4); standing partition (4.1), p. 10

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem theorem_4_8 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hMh : M.IsHermitian) (hNh : N.IsHermitian) :
    ((∃ α : ℝ, (M - α • N).PosSemidef) → ZZero N ⊆ ZSet M) ∧
    (Nonempty ι → InPi M → InPi N → schur N = 0 →
      (∀ v : ι → ℝ, Theta M N *ᵥ v = 0 → schur M *ᵥ v = 0) →
      (ZZero N ⊆ ZSet M ↔ ∃ α : ℝ, 0 ≤ α ∧ (M - α • N).PosSemidef)) := by sorry
end QuadMatIneq.Finsler
