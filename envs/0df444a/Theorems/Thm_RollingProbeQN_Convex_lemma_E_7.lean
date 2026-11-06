-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_E_7
-- name    : RollingProbeQN.Convex.lemma_E_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:27:53.777422+00:00
-- url     : https://prove2.me/theorems/0ffca512-a6c7-4c42-8761-4f939f3f6970
-- title:
--   Lemma E.7 — pointwise inverse-stepsize bound (55)
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with Subroutine 1.1, any $b>0$ and $\sigma\in(0,1)$. At every executed iteration $k$, with $m_k=\|y_k-x_k\|$, $g_k=\|\nabla f(x_k)\|$ and $E_k=\min\{L_1,\bar E_k+L_2m_k\}$,
--
--   $$\lambda_k^{-1}\ \le\ \frac{10E_k}{\sigma}+\sqrt{\frac{5L_2g_k}{\sigma}}+\frac{5L_2m_k}{\sigma}+\sqrt{\frac{5L_2\bar E_km_k}{\sigma}}+\frac{L_2m_k}{2}\sqrt{\frac{10}{\sigma}} .\tag{55}$$
--
--   This inverts near-maximality into the bound that the counting argument of Appendix E.3 sums over each mass scale.
--
--   Differences from the source:
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma E.7, p. 48

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_iterAt
import Definitions.Def_RollingProbeQN_Convex_Active

namespace RollingProbeQN.Convex

/-- **Lemma E.7 (Pointwise inverse-stepsize bound), (55).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma E.7, p. 48: "At every iteration of Algorithm 1 with Subroutine 1.1, let
`m_k = m(λ_k) = ‖y_k − x_k‖`, `g_k = ‖∇f(x_k)‖` and `E_k = E_k(λ_k) = min{L1, Ē_k + L2 m_k}`. Then
`λ_k^{−1} ≤ 10E_k/σ + √(5L2 g_k/σ) + 5L2 m_k/σ + √(5L2 Ē_k m_k/σ) + (L2 m_k/2)√(10/σ)`." (55)

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, b, σ⟩`, for
any allowance `b > 0` and `σ ∈ (0, 1)` (Algorithm 1 fixes `b > 0`, p. 9); `st` is the state at the
start of iteration `k` and `D` the quantities of iteration `k`. "An iteration `k` of Algorithm 1" is an
executed iteration (`Active`: the run has not returned and `∇f(x_k) ≠ 0`). -/
theorem lemma_E_7 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R b σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hb : 0 < b) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (hk : Active (⟨grp, S, L₁, L₂, b, σ⟩ : Config d χ) (gradient f) x₀ k) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, b, σ⟩
    let st := run cfg (gradient f) x₀ k
    let D := iterAt cfg (gradient f) x₀ k
    D.lam⁻¹ ≤ 10 * min L₁ (D.Ebar + L₂ * ‖D.y - st.x‖) / σ
      + Real.sqrt (5 * L₂ * ‖gradient f st.x‖ / σ) + 5 * L₂ * ‖D.y - st.x‖ / σ
      + Real.sqrt (5 * L₂ * D.Ebar * ‖D.y - st.x‖ / σ)
      + L₂ * ‖D.y - st.x‖ / 2 * Real.sqrt (10 / σ) := by sorry

end RollingProbeQN.Convex
