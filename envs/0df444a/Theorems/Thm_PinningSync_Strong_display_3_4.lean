-- Prove2me | Theorems.Thm_PinningSync_Strong_display_3_4
-- name    : PinningSync.Strong.display_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:31.207303+00:00
-- url     : https://prove2.me/theorems/fe719c6e-97a3-490e-94b4-6d803ff8f0b8
-- title:
--   (3.4), proof of Theorem 3.1, p. 1402 — along the error dynamics, V̇ ≤ eᵀ[Ξ ⊗ (KΓ) + c(Ĝ − ΞD) ⊗ Γ]e (Γ symmetric)
-- statement:
--   Let $f$ satisfy Assumption 1 with matrices $K,\Gamma\in\mathbb R^{n\times n}$, where $\Gamma$ is symmetric. Let $G$ be a coupling matrix, $c\in\mathbb R$ the coupling strength, $d\in\mathbb R^N$ the control gains, $D=\operatorname{diag}(d)$, and $\xi\in\mathbb R^N$ with all $\xi_i>0$, $\Xi=\operatorname{diag}(\xi)$, $\widehat G=\tfrac12(\Xi G+G^T\Xi)$. Let $s$ solve the isolated system (2.4) and $x$ solve the controlled network (2.5)–(2.6). Write $e_i(t)=x_i(t)-s(t)$, $e(t)=(e_1(t)^T,\dots,e_N(t)^T)^T$, and
--   $$
--   V(t)=\tfrac12\sum_{i=1}^N\xi_i\,e_i(t)^Te_i(t).
--   $$
--   Then for every $t\ge 0$, $V$ is differentiable at $t$ (from the right at $t=0$) and its derivative satisfies
--   $$
--   \dot V(t)\le e(t)^T\Bigl[\Xi\otimes(K\Gamma)+c\,(\widehat G-\Xi D)\otimes\Gamma\Bigr]e(t).
--   $$
--
--   This is the derivative estimate (3.4) from which Theorem 3.1 follows.
--
--   **Formalization Note.** The paper's proof replaces $\sum_i\xi_ie_i^T\sum_jG_{ij}\Gamma e_j$ by the quadratic form of $\widehat G\otimes\Gamma$; the two agree for every $e$ only when $\Gamma$ (or $\Xi G$) is symmetric, so $\Gamma^T=\Gamma$ is assumed, as in the mission's version of Theorem 3.1. The estimate holds for any positive weights $\xi$, so neither the zero-row-sum property of $\widehat G$ nor strong connectivity nor the sign of the gains is assumed here. The derivative is the derivative within $[0,\infty)$.
-- source:
--   Yu, Chen, Lü, Kurths, Synchronization via pinning control on general complex networks, SIAM J. Control Optim. 51 (2013), p. 1402, proof of Theorem 3.1, (3.3) and (3.4)

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace PinningSync.Strong

open Matrix Kronecker

theorem display_3_4 {N n : ℕ} (f : (Fin n → ℝ) → ℝ → (Fin n → ℝ))
    (K Γ : Matrix (Fin n) (Fin n) ℝ) (hA1 : Assumption1 f K Γ) (hΓ : Γᵀ = Γ) (c : ℝ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsCouplingMatrix G) (d : Fin N → ℝ)
    (ξ : Fin N → ℝ) (hξ : ∀ i, 0 < ξ i)
    (s : ℝ → Fin n → ℝ) (x : ℝ → Fin N → Fin n → ℝ)
    (hs : IsIsolatedSolution f s) (hx : IsControlledSolution f c G Γ d s x) :
    ∀ t : ℝ, 0 ≤ t → ∃ v : ℝ, HasDerivWithinAt (lyapV ξ s x) v (Set.Ici 0) t ∧
      v ≤ errStack s x t ⬝ᵥ
        ((diagonal ξ ⊗ₖ (K * Γ) + c • ((Ghat G ξ - diagonal ξ * diagonal d) ⊗ₖ Γ))
          *ᵥ errStack s x t) := by sorry

end PinningSync.Strong
