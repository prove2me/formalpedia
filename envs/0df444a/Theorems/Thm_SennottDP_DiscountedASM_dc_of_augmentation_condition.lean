-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_dc_of_augmentation_condition
-- name    : SennottDP.DiscountedASM.dc_of_augmentation_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:58:17.011393+00:00
-- url     : https://prove2.me/theorems/f9cd0f74-f314-43aa-9a15-e70e7fa43055
-- title:
--   Proposition 4.7.6 — the augmentation condition (3.20) gives $V^N_\alpha\le V_\alpha$ and DC($\alpha$)
-- statement:
--   Let $\Delta$ be an MDC with countable state space and $\alpha\in(0,1)$, and assume $V_\alpha(i)<\infty$ for every state $i$. Let $v_{\alpha,n}$ be the $n$-horizon discounted value function of $\Delta$ with terminal cost $0$. Let $(\Delta_N)_{N\ge N_0}$ be an ATAS whose augmentation distributions satisfy
--   $$
--   \sum_{j\in S_N}q_j(i,a,r,N)\,v_{\alpha,n}(j)\le v_{\alpha,n}(r),\qquad i\in S_N,\ a\in A_i,\ r\in S-S_N,\ n\ge0. \tag{3.20}
--   $$
--   Then
--   $$
--   V^N_\alpha(i)\le V_\alpha(i),\qquad i\in S_N,
--   $$
--   and hence Assumption DC($\alpha$) holds.
--
--   Condition (3.20) says that redistributing the excess probability from an outside state $r$ never produces a weighted value larger than the value at $r$ itself; it holds for instance when values increase in the state and the excess is sent to a smaller state.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 81, Proposition 4.7.6; p. 49, equation (3.20)

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Proposition 4.7.6 (p. 81): if `V_α < ∞` and `(Δ_N)` is an ATAS whose augmentation
distributions satisfy (3.20),
`Σ_{j ∈ S_N} q_j(i,a,r,N) v_{α,n}(j) ≤ v_{α,n}(r)` for `i ∈ S_N`, `a ∈ A_i`, `r ∈ S - S_N`,
`n ≥ 0` (with `v_{α,n}` the `n`-horizon value function with terminal cost `0`), then
`V^N_α(i) ≤ V_α(i)` for `i ∈ S_N`, and hence DC(α) holds. -/
theorem dc_of_augmentation_condition {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (h320 : ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ Δs.SN N → ∀ n : ℕ,
      ∑ j ∈ Δs.SN N, q N i a r j * M.horizonValue α n j ≤ M.horizonValue α n r) :
    (∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, Δs.VN α N i ≤ M.value α i) ∧ Δs.DC α := by sorry

end SennottDP.DiscountedASM
