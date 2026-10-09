-- Prove2me | Theorems.Thm_PinningSync_Tree_theorem_4_5
-- name    : PinningSync.Tree.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:37.62514+00:00
-- url     : https://prove2.me/theorems/ca3f0869-776d-452a-95fb-d07511212b57
-- title:
--   Theorem 4.5, p. 1406 — 2θΠ̃ⱼ + c(Π̃ⱼG̃ⱼ + G̃ⱼᵀΠ̃ⱼ) < 0 on every strongly connected component globally synchronizes the pinned network with a directed spanning tree
-- statement:
--   Consider the controlled network (2.5)–(2.6): vertices $1,\dots,N$ with states in $\mathbb R^n$, a continuously differentiable $f:\mathbb R^n\times\mathbb R_+\to\mathbb R^n$, coupling strength $c$, inner coupling matrix $\Gamma$, coupling configuration matrix $G$ as in (2.2), and pinning gains $d_i\ge 0$. Assume:
--
--   1. Assumption 1 holds with a matrix $K$, $\Gamma$ is positive definite, $K\Gamma=\Gamma K$, and $\theta=\lambda_{\max}((K+K^{\mathsf T})/2)\ge 0$ (the standing assumptions of p. 1402);
--   2. the network augmented by the virtual leader $s$ (joined to each pinned vertex) has a directed spanning tree rooted at the leader;
--   3. the vertices are partitioned into the strongly connected components $V_1,\dots,V_M$ (all nonempty), listed in the order of the Frobenius normal form (4.3);
--   4. for each component $j$, $\Pi_j$ is a positive vector with $\Pi_j^{\mathsf T}A_j=0$, where $A_j$ is the zero row-sum within-component part of $G$, and $\widetilde\Pi_j=\mathrm{diag}(\Pi_j)$.
--
--   Let $\widetilde G_j$ be the diagonal block of $G-\mathrm{diag}(d)$ on $V_j$. If
--   $$
--   2\theta\widetilde\Pi_j+c\bigl(\widetilde\Pi_j\widetilde G_j+\widetilde G_j^{\mathsf T}\widetilde\Pi_j\bigr)<0\qquad\text{for every component } j,\tag{4.8}
--   $$
--   then the controlled network is globally synchronized: for every solution $s$ of $\dot s=f(s,t)$ and every solution $x$ of (2.5), $x_i(t)-s(t)\to0$ as $t\to\infty$ for every vertex $i$.
--
--   The condition reduces synchronization of the whole network to one linear matrix inequality per strongly connected component, each of the size of that component.
--
--   **Formalization Note** "For any initial conditions" is read as: for every pair of solutions $(s,x)$ on $[0,\infty)$; existence of solutions is not part of the claim. "Positive definite" for $\Gamma$ is Mathlib's `Matrix.PosDef`, which includes symmetry, the convention of p. 1400. The vertices are not reordered into Frobenius form: `blk` records each vertex's component, and the hypotheses say that every component is strongly connected inside itself and that edges between distinct components only point forward in the order. Component `j : Fin M` is the paper's component $j+2$; "$j=2,\dots,m$" is every component. Negative definiteness of $X$ is positive definiteness of $-X$. For $n=0$ the λ_max hypothesis cannot be met.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1406, Theorem 4.5 and (4.8); standing assumptions p. 1402; setting pp. 1404–1405

import Mathlib
import Definitions.Def_PinningSync_Tree_Setting

open Matrix Kronecker Filter Topology

namespace PinningSync.Tree

theorem theorem_4_5 {N n M : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (hf : ContDiffOn ℝ 1 (fun p : (Fin n → ℝ) × ℝ => f p.1 p.2) (Set.univ ×ˢ Set.Ici 0))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : PinningSync.Strong.Assumption1 f K Γ) (hΓ : Γ.PosDef)
    (hKΓ : K * Γ = Γ * K) (θ : ℝ) (hθ : PinningSync.Strong.IsLamMax ((1 / 2 : ℝ) • (K + Kᵀ)) θ) (hθ0 : 0 ≤ θ)
    (c : ℝ) (G : Matrix (Fin N) (Fin N) ℝ) (hG : PinningSync.Strong.IsCouplingMatrix G)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (hst : HasLeaderSpanningTree G d)
    (blk : Fin N → Fin M) (hsurj : Function.Surjective blk)
    (hblk : IsBlockLowerTriangular G blk) (hscc : BlocksStronglyConnected G blk)
    (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i)
    (hπA : ∀ j, Matrix.vecMul (fun a : Blk blk j => π a.val) (Ablk G blk j) = 0)
    (h48 : ∀ j, cond48 θ c G d π blk j) :
    ∀ (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ),
      PinningSync.Strong.IsIsolatedSolution f s → PinningSync.Strong.IsControlledSolution f c G Γ d s x → PinningSync.Strong.GloballySynchronized s x := by sorry

end PinningSync.Tree
