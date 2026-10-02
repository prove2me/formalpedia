-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_dc_of_atas_finite_set
-- name    : SennottDP.DiscountedASM.dc_of_atas_finite_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T07:53:36.470091+00:00
-- url     : https://prove2.me/theorems/ff06af27-b03d-4f09-94e4-c332cfb322ff
-- title:
--   Proposition 4.7.4 — an ATAS sending excess probability to a finite set satisfies DC($\alpha$)
-- statement:
--   Let $\Delta$ be an MDC with countable state space and $\alpha\in(0,1)$, and assume $V_\alpha(i)<\infty$ for every state $i$. Let $(\Delta_N)_{N\ge N_0}$ be an augmentation type approximating sequence (ATAS) for $\Delta$ that sends excess probability to a finite set $G$, i.e. every augmentation distribution satisfies $\sum_{j\in G}q_j(i,a,r,N)=1$. Then Assumption DC($\alpha$) holds:
--   $$
--   \limsup_{N\to\infty}V^N_\alpha(i)<\infty\quad\text{and}\quad\limsup_{N\to\infty}V^N_\alpha(i)\le V_\alpha(i),\qquad i\in S.
--   $$
--
--   No bound on the costs is assumed: this is the result that makes the method usable for queueing models with unbounded holding costs, where the natural truncation redirects overflow to a few fixed states.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 79, Proposition 4.7.4

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Proposition 4.7.4 (p. 79): if `V_α < ∞` and `(Δ_N)` is an ATAS that sends excess
probability to a finite set, then DC(α) holds. -/
theorem dc_of_atas_finite_set {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hV : ∀ i, M.value α i < ⊤)
    (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : Δs.IsATAS q)
    (G : Finset S) (hG : Δs.SendsExcessTo q G) :
    Δs.DC α := by sorry

end SennottDP.DiscountedASM
