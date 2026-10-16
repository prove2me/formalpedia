-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_pi22_lt_pi22_zN
-- name    : SoftenDataShare.Mutual.pi22_lt_pi22_zN
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:06.525341+00:00
-- url     : https://prove2.me/theorems/3361392c-4a56-4843-9a05-d400951a49c7
-- title:
--   Proof of Proposition 1, p. 35 — π̂₂₂(b) < π̂₂₂(z^N) for every b ∈ (z^N, 1]
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ and $z^N$ the benchmark marginal consumer of Eq. (1). With $\hat\pi_{22}(b)=\pi_{22}(z^N,b)$ as above, for every $b$ with $z^N<b\le1$,
--   $$\hat\pi_{22}(b)<\hat\pi_{22}(z^N)=\pi_{21}(z^N).$$
--
--   Sharing more of firm 2's customer base strictly lowers what firm 2 can earn by competing for consumers in $[z',z^N]$. This is the step from which the paper derives the existence of an interval $[z^N,b']$ satisfying firm 2's incentive constraint.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 35, proof of Proposition 1

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem pi22_lt_pi22_zN {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    ∀ b ∈ Set.Ioc zN 1, pi22 F zN b < pi22 F zN zN := by sorry

end SoftenDataShare.Mutual
