-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_pi22_boundary
-- name    : SoftenDataShare.Mutual.pi22_boundary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:10.285641+00:00
-- url     : https://prove2.me/theorems/d8798815-9713-48ef-8e3a-71150b08558a
-- title:
--   Proof of Proposition 1, p. 35 — π₂₁(z^N) = π̂₂₂(z^N) and π₂₁(1) < π̂₂₂(1), where π̂₂₂(b) = π₂₂(z^N, b)
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ and $z^N$ the benchmark marginal consumer of Eq. (1). Fix $a=z^N$ and write $\hat\pi_{22}(b)=\pi_{22}(z^N,b)=\max_{z'\in[0,z^N]}(2z'-1)(1-F(b)+F(z^N)-F(z'))$. Then
--   $$\pi_{21}(z^N)=\hat\pi_{22}(z^N)\qquad\text{and}\qquad\pi_{21}(1)<\hat\pi_{22}(1).$$
--
--   At the two ends of the range of $b$, firm 2's two pricing options compare in opposite ways: at $b=z^N$ they tie, and at $b=1$ (all of firm 2's base shared) competing for $[z',z^N]$ is strictly better. So an interval satisfying firm 2's incentive constraint (IC), if one exists, has $b<1$.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 35, proof of Proposition 1

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem pi22_boundary {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    pi21 F zN = pi22 F zN zN ∧ pi21 F 1 < pi22 F zN 1 := by sorry

end SoftenDataShare.Mutual
