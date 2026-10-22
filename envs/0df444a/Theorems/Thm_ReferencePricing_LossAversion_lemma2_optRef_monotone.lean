-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_lemma2_optRef_monotone
-- name    : ReferencePricing.LossAversion.lemma2_optRef_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:49:44.898198+00:00
-- url     : https://prove2.me/theorems/4f2cc817-49e7-4bbf-a9b6-63e363272f4a
-- title:
--   Lemma 2 — the optimal reference price policy $q^*(r)$ is increasing in $r$
-- statement:
--   Consider the loss-neutral dynamic pricing problem (2) on $P=[0,\bar p]$ with $\alpha\in[0,1)$ and $\beta\in(0,1)$. The demand is $D(p,r)=d(p)+R(r-p,r)$ with $d$ differentiable, and Assumptions 1, 2 and 3 hold. Let $p^*(r)$ be the largest maximizer of $W(\cdot,r)$ over $P$, and let $q^*(r)=\alpha r+(1-\alpha)p^*(r)$ be the next reference price it induces. Then
--   $$
--   r,r'\in P,\ r\le r'\ \Longrightarrow\ q^*(r)\le q^*(r').
--   $$
--
--   Monotonicity of $q^*$ is what makes every optimal state path monotone. It is the first step towards the global stability result, Theorem 2.
--
--   **Formalization Note** "Increases" is non-strict (`MonotoneOn` on $P$). The hypothesis that $d$ is differentiable is added. The paper uses $\pi'$ in Assumption 3(b) without stating it, and Lean's `deriv` is $0$ at points of non-differentiability.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 419, Lemma 2 (proof in Appendix A.5, p. 426)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Lemma 2 (Monotone Reference Price Policy), Popescu and Wu 2007, p. 419: under
Assumptions 1–3 the reference price policy `q*(r) = α r + (1 − α) p*(r)`, with `p*` the largest
maximizer of (2), is increasing in `r` on `P = [0, p̄]`. -/
theorem lemma2_optRef_monotone (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d) (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R)
    (hA3 : Assumption3 pbar d R) :
    MonotoneOn (optRef (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by sorry

end ReferencePricing.LossAversion
