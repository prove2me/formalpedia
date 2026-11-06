-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_E_4
-- name    : RollingProbeQN.Convex.lemma_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:42.77952+00:00
-- url     : https://prove2.me/theorems/8a66c439-3820-40a6-b3d6-cb29f76b4188
-- title:
--   Lemma E.4 — the resolvent certificate $\|r(\lambda)\|\le\widehat\rho_k(\lambda)$ of (9)
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with any $b>0$, $\sigma\in(0,1)$, and fix an executed iteration $k$ and $\lambda>0$. With $y(\lambda)$, $m(\lambda)$ as in Lemma E.3 and $g_k=\|\nabla f(x_k)\|$, the model step $r(\lambda)=-(B_k+\lambda^{-1}I)^{-1}\nabla f(y(\lambda))$ satisfies
--
--   $$\|r(\lambda)\|\ \le\ \widehat\rho_k(\lambda):=\lambda g_k+m(\lambda)\Big(1+\lambda\bar E_k+\frac{L_2\lambda}{2}m(\lambda)\Big).$$
--
--   This bounds the second term of (6) by stored data.
--
--   Differences from the source:
--   - encoding: the lemma's hypotheses B_k ∈ Z and ‖B_k − H(x_k)‖op ≤ Ē_k → not hypotheses: the statement is about the run, where they hold; reason: they hold at every executed iteration by (4) and Lemma E.1
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma E.4, p. 46

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_iterAt
import Definitions.Def_RollingProbeQN_Convex_Active
import Definitions.Def_RollingProbeQN_Convex_mOf

namespace RollingProbeQN.Convex

/-- **Lemma E.4 (The resolvent certificate).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma E.4, p. 46: "Fix an iteration `k` of Algorithm 1 and `λ > 0`. Let
`y(λ) = (A_k x_k + a(λ) z_k)/(A_k + a(λ))` and `m(λ) = ‖y(λ) − x_k‖` be as in Lemma E.3, let
`B_k ∈ Z` be the current model with certificate `‖B_k − H(x_k)‖op ≤ Ē_k`, and let
`g_k = ‖∇f(x_k)‖`. Then the model step `r(λ) = −(B_k + λ^{−1}I)^{−1}∇f(y(λ))` satisfies
`‖r(λ)‖ ≤ ρ̂_k(λ) := λ g_k + m(λ)(1 + λĒ_k + (L2λ/2) m(λ))`, which is the bound (9)."

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, b, σ⟩`, for
any allowance `b > 0` and `σ ∈ (0, 1)` (Algorithm 1 fixes `b > 0`, p. 9); `st` is the state at the
start of iteration `k` and `D` the quantities of iteration `k`. "An iteration `k` of Algorithm 1" is an
executed iteration (`Active`: the run has not returned and `∇f(x_k) ≠ 0`). `m(λ)` is `mOf A_k ζ_k λ` (equal to `‖y(λ) − x_k‖` by Lemma E.3). -/
theorem lemma_E_4 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R b σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hb : 0 < b) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (hk : Active (⟨grp, S, L₁, L₂, b, σ⟩ : Config d χ) (gradient f) x₀ k) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, b, σ⟩
    let st := run cfg (gradient f) x₀ k
    let D := iterAt cfg (gradient f) x₀ k
    ∀ lam : ℝ, 0 < lam →
      ‖modelStep D.B lam (gradient f (yOf st.A st.x st.z lam))‖ ≤
        lam * ‖gradient f st.x‖ + mOf st.A ‖st.z - st.x‖ lam *
          (1 + lam * D.Ebar + L₂ * lam / 2 * mOf st.A ‖st.z - st.x‖ lam) := by sorry

end RollingProbeQN.Convex
