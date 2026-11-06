-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_E_6
-- name    : RollingProbeQN.Convex.lemma_E_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:37.325464+00:00
-- url     : https://prove2.me/theorems/8cd23f3f-33f8-44dc-a5ac-4411d712f6f9
-- title:
--   Lemma E.6 — Subroutine 1.1 costs $O(\log\log)$ evaluations, no gradient, and returns a nearly maximal admissible stepsize
-- statement:
--   Under Assumption 2.1, run Algorithm 1 with any $b>0$, $\sigma\in(0,1)$. At every executed iteration $k$, with $W_k=\log(L_1/\bar E_k)$:
--
--   1. Subroutine 1.1 evaluates $\widehat\Psi_k$ at most $1+\big\lceil\log_2\max\{1,\,W_k/\log 2^{1/4}\}\big\rceil$ times (and uses no gradient query);
--   2. the returned stepsize satisfies the relative condition (2): $\|x_{k+1}-y_k+\lambda_k\nabla f(x_{k+1})\|\le\sigma\|x_{k+1}-y_k\|$;
--   3. $\sigma/L_1\le\lambda_k\le\sigma/\bar E_k$;
--   4. $\widehat\Psi_k(\lambda_k)\ge\sigma/2$.
--
--   Here $\widehat\Psi_k$ is the surrogate (10) with inputs $A_k$, $\zeta_k$, $g_k=\|\nabla f(x_k)\|$, $\bar E_k$. Near-maximality (4) is the form in which the stepsize choice enters the rate.
--
--   Differences from the source:
--   - encoding: Subroutine 1.1 uses no gradient queries → not a clause: subroutine11 takes the scalars A_k, ζ_k, g_k, Ē_k only; reason: the property holds by the type of the subroutine
--   - encoding: Step 1 returns x_k when ∇f(x_k) = 0; the iterates after a return do not exist → the run is frozen at the return; statements about an iteration assume it is executed (Active); reason: B_k, Ē_k, λ_k, y_k, r_k are formed only at executed iterations (reading R2)
--   - encoding: refreshed group i_k = (k mod χ) + 1, groups g_1, …, g_χ → 0-based label k % χ of grp : Fin d → Fin χ; reason: relabelling of the groups (reading R5)
--   - encoding: Π_Z clips the eigenvalues of a symmetric matrix to [0, L₁] → clipZ L₁, the functional calculus of t ↦ min (max t 0) L₁ (0 on non-symmetric input); reason: the same map on symmetric matrices, the only input it receives (reading R6)
--   - encoding: a partition g₁, …, g_χ of [d] → a surjective map grp : Fin d → Fin χ with 0 < χ; reason: a partition has no empty block (reading R7)
--   - encoding: the while loop of Subroutine 1.1 → a guarded bisection pass iterated ⌈4 log(L₁/Ē_k)/log 2⌉ + 1 times; reason: the loop ends within that many passes (Lemma E.6's count) and further passes change nothing (reading R8)
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma E.6, p. 47

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Assumption21
import Definitions.Def_RollingProbeQN_Convex_iterAt
import Definitions.Def_RollingProbeQN_Convex_Active

namespace RollingProbeQN.Convex

/-- **Lemma E.6 (Subroutine 1.1: count, admissibility, bracket, near-maximality).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma E.6, p. 47: "Subroutine 1.1 uses no gradient queries and at most
`1 + ⌈log2(max{1, W_k/log(2^{1/4})})⌉` evaluations of `Ψ̂_k`, where `W_k = log(L1/Ē_k)`. The returned
stepsize satisfies the relative condition (2), and `σ/L1 ≤ λ_k ≤ σ/Ē_k`, `Ψ̂_k(λ_k) ≥ σ/2`."

At every executed iteration `k`: the number of evaluations of `Ψ̂_k` spent by Subroutine 1.1 is at
most `1 + ⌈log₂ max{1, W_k/log 2^{1/4}}⌉`; the pair `(y_k, x_{k+1})` satisfies (2); and
`σ/L₁ ≤ λ_k ≤ σ/Ē_k` and `Ψ̂_k(λ_k) ≥ σ/2`, where `Ψ̂_k = surrogate L₁ L₂ A_k ζ_k g_k Ē_k`.

**Formalization Note.** The run is `run cfg (gradient f) x₀` with `cfg = ⟨grp, S, L₁, L₂, b, σ⟩`, for
any allowance `b > 0` and `σ ∈ (0, 1)` (Algorithm 1 fixes `b > 0`, p. 9); `st` is the state at the
start of iteration `k` and `D` the quantities of iteration `k`. "An iteration `k` of Algorithm 1" is an
executed iteration (`Active`: the run has not returned and `∇f(x_k) ≠ 0`). "Uses no gradient queries" holds by construction: `subroutine11` takes the scalars
`A_k, ζ_k, g_k, Ē_k` only (encoding). The evaluation count is the counter returned by
`subroutine11`. -/
theorem lemma_E_6 {d χ : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L₁ L₂ R b σ : ℝ}
    {S : Set (Fin d × Fin d)} {grp : Fin d → Fin χ} {x₀ xstar : EuclideanSpace ℝ (Fin d)}
    (hA : Assumption21 d χ f L₁ L₂ R S grp x₀ xstar) (hb : 0 < b) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (hk : Active (⟨grp, S, L₁, L₂, b, σ⟩ : Config d χ) (gradient f) x₀ k) :
    let cfg : Config d χ := ⟨grp, S, L₁, L₂, b, σ⟩
    let st := run cfg (gradient f) x₀ k
    let D := iterAt cfg (gradient f) x₀ k
    D.nEval ≤ 1 + ⌈Real.logb 2 (max 1 (Real.log (L₁ / D.Ebar) / Real.log ((2 : ℝ) ^ ((1 : ℝ) / 4))))⌉₊ ∧
    ‖D.x' - D.y + D.lam • gradient f D.x'‖ ≤ σ * ‖D.x' - D.y‖ ∧
    σ / L₁ ≤ D.lam ∧ D.lam ≤ σ / D.Ebar ∧
    σ / 2 ≤ surrogate L₁ L₂ st.A ‖st.z - st.x‖ ‖gradient f st.x‖ D.Ebar D.lam := by sorry

end RollingProbeQN.Convex
