-- Prove2me | Theorems.Thm_PinningSync_Tree_display_4_10
-- name    : PinningSync.Tree.display_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:36.827125+00:00
-- url     : https://prove2.me/theorems/6404e146-1eb4-4a39-94d4-33bf0917edf4
-- title:
--   (4.10), proof of Theorem 4.5, p. 1407 — V(t) = Σ Δ eᵀΠ̃e has V̇ ≤ eᵀ{[ΔΠ̃(cḠ + θI_N) + (cḠ + θI_N)ᵀΠ̃Δ] ⊗ Γ}e
-- statement:
--   Consider the controlled network (2.5)–(2.6) with coupling matrix $G$ (zero row sums, nonnegative off-diagonal), pinning gains $d_i$, inner coupling $\Gamma$ positive definite, and $f$ satisfying Assumption 1 with $K\Gamma=\Gamma K$ and $\theta=\lambda_{\max}((K+K^{\mathsf T})/2)$. Let $s$ solve (2.4) and $x$ solve (2.5), and let $e_i(t)=x_i(t)-s(t)$. Assign each vertex $i$ to a component $\mathrm{blk}(i)$, and fix positive numbers $\pi_i$ and positive constants $\Delta_j$ per component. Put $w_i=\Delta_{\mathrm{blk}(i)}\pi_i$, $\overline G=G-\widetilde D$ with $\widetilde D=\mathrm{diag}(d_i)$, and
--   $$
--   V(t)=\sum_{i=1}^N w_i\,e_i(t)^{\mathsf T}e_i(t),\tag{4.9}
--   $$
--   which is $\sum_j\Delta_j\widetilde e_j^{\mathsf T}\widetilde\Pi_j\widetilde e_j$. Then for every $t\ge0$, $V$ is differentiable at $t$ (from the right at $t=0$) and, with $W=\mathrm{diag}(w)=\Delta\widetilde\Pi$ and $e=(e_1^{\mathsf T},\dots,e_N^{\mathsf T})^{\mathsf T}$,
--   $$
--   \dot V(t)\le e(t)^{\mathsf T}\Bigl\{\bigl[W(c\overline G+\theta I_N)+(c\overline G+\theta I_N)^{\mathsf T}W\bigr]\otimes\Gamma\Bigr\}e(t).\tag{4.10}
--   $$
--
--   This is the derivative estimate of the Lyapunov function in the proof of Theorem 4.5; together with Lemma 4.4 it shows $V$ decays.
--
--   **Formalization Note** The page lists the vertices component by component; here the original order is kept and the component weights enter through `blk`, which gives the same quadratic form after a permutation. The printed chain has two misprints: its third line reads "$-\,c(\Delta\widetilde\Pi\overline G+\overline G^{\mathsf T}\widetilde\Pi\Delta)$" and its last line "$(c\overline G++\theta I_N)$"; the statement uses the last line with a single $+$, which is what the second line gives. The Kronecker product is indexed by pairs (vertex, coordinate), which matches the stacking of $e$. The hypotheses on the Frobenius form, the spanning tree, $\theta\ge0$, and the smoothness of $f$ are not needed for this estimate and are omitted.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1406–1407, proof of Theorem 4.5, (4.9) and (4.10)

import Mathlib
import Definitions.Def_PinningSync_Tree_Setting

open Matrix Kronecker Filter Topology

namespace PinningSync.Tree

theorem display_4_10 {N n M : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : PinningSync.Strong.Assumption1 f K Γ) (hΓ : Γ.PosDef)
    (hKΓ : K * Γ = Γ * K) (θ : ℝ) (hθ : PinningSync.Strong.IsLamMax ((1 / 2 : ℝ) • (K + Kᵀ)) θ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : PinningSync.Strong.IsCouplingMatrix G) (d : Fin N → ℝ)
    (blk : Fin N → Fin M) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i)
    (Δ : Fin M → ℝ) (hΔ : ∀ j, 0 < Δ j)
    (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ)
    (hs : PinningSync.Strong.IsIsolatedSolution f s) (hx : PinningSync.Strong.IsControlledSolution f c G Γ d s x) :
    let e : ℝ → Fin N → Fin n → ℝ := fun t i => x t i - s t
    let w : Fin N → ℝ := fun i => Δ (blk i) * π i
    let V : ℝ → ℝ := fun t => ∑ i, w i * (e t i ⬝ᵥ e t i)
    let Gbar : Matrix (Fin N) (Fin N) ℝ := G - diagonal d
    let A : Matrix (Fin N) (Fin N) ℝ := c • Gbar + θ • (1 : Matrix (Fin N) (Fin N) ℝ)
    let Mq : Matrix (Fin N) (Fin N) ℝ := diagonal w * A + Aᵀ * diagonal w
    ∀ t : ℝ, 0 ≤ t → ∃ v : ℝ, HasDerivWithinAt V v (Set.Ici 0) t ∧
      v ≤ (fun p : Fin N × Fin n => e t p.1 p.2) ⬝ᵥ
        ((Mq ⊗ₖ Γ) *ᵥ fun p : Fin N × Fin n => e t p.1 p.2) := by sorry

end PinningSync.Tree
