-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_E_1
-- name    : RollingProbeQN.Convex.lemma_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:28.21521+00:00
-- url     : https://prove2.me/theorems/66de6c6b-6ba8-4415-9521-697a3cdac0c2
-- title:
--   Lemma E.1 — the rolling certificate: $\|B_k-H(x_k)\|_{\mathrm{op}}\le\bar E_k$
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with any allowance $b>0$ and $\sigma\in(0,1)$. At every executed iteration $k$,
--
--   $$\|B_k-H(x_k)\|_{\mathrm{op}}\ \le\ \bar E_k,$$
--
--   with $\bar E_k$ given by (5). Moreover $B_k\in\mathcal Z$ and $0<\bar E_k\le L_1$.
--
--   The certificate is computed from stored data before any new gradient is queried; it is what makes the stepsize choice gradient-free.
--
--   Differences from the source:
--   - generalization: ‖B_k − H(x_k)‖op ≤ Ē_k → the bound together with B_k ∈ Z and 0 < Ē_k ≤ L₁; reason: B_k ∈ Z holds by (4) (p. 9) and 0 < Ē_k ≤ L₁ is recorded on p. 47; dropping these clauses gives the source's statement
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma E.1, p. 43

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_InZ
import Definitions.Def_RollingProbeQN_Convex_iterAt
import Definitions.Def_RollingProbeQN_Convex_Active

namespace RollingProbeQN.Convex

/-- **Lemma E.1 (The rolling curvature certificate).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma E.1, p. 43: "For all `k ≥ 0`, we have `‖B_k − H(x_k)‖op ≤ Ē_k`, with `Ē_k` given by
(5)."

Along the run of Algorithm 1 under Assumption 2.1, at every executed iteration `k`:
`‖B_k − H(x_k)‖op ≤ Ē_k`; moreover `B_k ∈ Z` (by (4), p. 9) and `0 < Ē_k ≤ L₁` (recorded in the proof of
Lemma E.6, p. 47).

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, b, σ⟩`, for
any allowance `b > 0` and `σ ∈ (0, 1)` (Algorithm 1 fixes `b > 0`, p. 9); `st` is the state at the
start of iteration `k` and `D` the quantities of iteration `k`. "An iteration `k` of Algorithm 1" is an
executed iteration (`Active`: the run has not returned and `∇f(x_k) ≠ 0`). The operator norm of `B_k` is the norm of `Matrix.toEuclideanCLM B_k`. -/
theorem lemma_E_1 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R b σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hb : 0 < b) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (hk : Active (⟨grp, S, L₁, L₂, b, σ⟩ : Config d χ) (gradient f) x₀ k) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, b, σ⟩
    let st := run cfg (gradient f) x₀ k
    let D := iterAt cfg (gradient f) x₀ k
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D.B - hess f st.x‖ ≤ D.Ebar ∧ InZ L₁ D.B ∧ 0 < D.Ebar ∧ D.Ebar ≤ L₁ := by sorry

end RollingProbeQN.Convex
