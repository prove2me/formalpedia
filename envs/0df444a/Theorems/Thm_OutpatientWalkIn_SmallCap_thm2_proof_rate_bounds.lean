-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_thm2_proof_rate_bounds
-- name    : OutpatientWalkIn.SmallCap.thm2_proof_rate_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:34.967244+00:00
-- url     : https://prove2.me/theorems/ea26ea28-17bc-450e-b3f4-50253742d2d7
-- title:
--   Online App. p. 28, proof of Theorem 2(1) — λ/(1 + λ/μ_S) ≤ λ[1 − π(δ, μ_S)] ≤ λ
-- statement:
--   Let $\lambda > 0$, $\mu_S > 0$ and $\delta \ge 0$, and let $\pi(\delta,\mu_S)$ be the blocking probability of the M/D/1/$\delta\mu_S$ queue with arrival rate $\lambda$ (Corollary C.1). Then
--   $$\frac{\lambda}{1+\lambda/\mu_S} \;\le\; \lambda\,[1-\pi(\delta,\mu_S)] \;\le\; \lambda .$$
--
--   The middle term is the rate $\lambda^o_S(\delta)$ at which strategic patients schedule when all of them use the threshold $\delta$. The lower bound does not depend on $\delta$. This is the estimate the proof of Theorem 2(1) combines with Lemma E.5 when capacity is small.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 28, proof of Theorem 2 (1), display after Corollary C.1

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue

namespace OutpatientWalkIn.SmallCap
theorem thm2_proof_rate_bounds (lam : ℝ) (hlam : 0 < lam) (δ : ℝ) (hδ : 0 ≤ δ) (μS : ℝ) (hμS : 0 < μS) :
    lam / (1 + lam / μS) ≤ lam * (1 - blockProb lam δ μS) ∧ lam * (1 - blockProb lam δ μS) ≤ lam := by sorry
end OutpatientWalkIn.SmallCap
