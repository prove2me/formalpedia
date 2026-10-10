-- Prove2me | Theorems.Thm_PinningSync_Strong_theorem_3_1
-- name    : PinningSync.Strong.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T07:26:56.467997+00:00
-- url     : https://prove2.me/theorems/b8fb877d-1285-473a-9f81-e51e0f4403c2
-- title:
--   Theorem 3.1, p. 1402 — under Assumption 1, the LMI (3.2) globally synchronizes the pinned strongly connected network (2.5) (Γ symmetric)
-- statement:
--   Let $f:\mathbb R^n\times\mathbb R_+\to\mathbb R^n$ be continuously differentiable and satisfy Assumption 1 with matrices $K,\Gamma\in\mathbb R^{n\times n}$, where the inner coupling matrix $\Gamma$ is symmetric. Let $G$ be a coupling matrix (2.2) whose network is strongly connected, let $c\in\mathbb R$ be the coupling strength and $d_1,\dots,d_N\ge 0$ the control gains (vertex $i$ is pinned iff $d_i>0$), $D=\operatorname{diag}(d_1,\dots,d_N)$. Let $\Xi=\operatorname{diag}(\xi_1,\dots,\xi_N)$ with all $\xi_i>0$ be such that $\widehat G=\tfrac12(\Xi G+G^T\Xi)$ has zero row sums (the matrix provided by Lemma 2.12). If
--   $$
--   \Xi\otimes\frac{K\Gamma+\Gamma^TK^T}{2}+c\,\widehat G\otimes\frac{\Gamma+\Gamma^T}{2}-c\,(\Xi D)\otimes\frac{\Gamma+\Gamma^T}{2}<0 \tag{3.2}
--   $$
--   (negative definite), then the controlled network is globally synchronized: for every solution $s$ of the isolated system $\dot s=f(s,t)$ and every solution $x$ of the controlled network (2.5)–(2.6),
--   $$
--   \lim_{t\to\infty}\|x_i(t)-s(t)\|=0\qquad(i=1,\dots,N).
--   $$
--
--   This is the main criterion of the paper's §3: one linear matrix inequality in the network data, weighted by the positive left null vector of $G$, certifies pinning synchronization of a directed strongly connected network.
--
--   **Formalization Note.** The symmetry $\Gamma^T=\Gamma$ is **added** to the printed statement, which allows any $\Gamma\in\mathbb R^{n\times n}$: without it the theorem is false (for $n=2$, $N=3$, $f\equiv0$, $K=0$, $G$ the directed 3-cycle, $\Xi=I$, $d=(1,0,0)$, $c=1$, $\Gamma=\begin{pmatrix}1&3\\-3&1\end{pmatrix}$, (3.2) holds but $(G-D)\otimes\Gamma$ has an eigenvalue with positive real part, so the error grows). Every example of the paper has symmetric $\Gamma$. "Ξ obtained by Lemma 2.12" is encoded by $\xi_i>0$ together with the zero row sums of $\widehat G$; for a matrix with zero row sums this is equivalent to $G^T\xi=0$. "For any initial conditions" is the quantification over every pair of solutions; existence of solutions is not asserted. "$M<0$" is positive definiteness of $-M$ (Mathlib's `PosDef`, which includes symmetry; the matrix in (3.2) is symmetric by construction).
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1402, Theorem 3.1 and (3.2)

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Strong

open Matrix

theorem theorem_3_1 {N n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hf : ContDiffOn ℝ 1 (fun p : (Fin n → ℝ) × ℝ => f p.1 p.2) (Set.univ ×ˢ Set.Ici 0))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : Assumption1 f K Γ) (hΓ : Γᵀ = Γ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsCouplingMatrix G) (hsc : IsStronglyConnected G)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ξ : Fin N → ℝ) (hξ : ∀ i, 0 < ξ i) (hΞ : ∀ i, ∑ j, Ghat G ξ i j = 0)
    (hlmi : (-(lmi32 K Γ c G ξ d)).PosDef) :
    ∀ (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ),
      IsIsolatedSolution f s → IsControlledSolution f c G Γ d s x →
        GloballySynchronized s x := by sorry

end PinningSync.Strong
