-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_pi2_sub_piN2
-- name    : SoftenDataShare.Mutual.pi2_sub_piN2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:10.776993+00:00
-- url     : https://prove2.me/theorems/ce18cee8-d30e-439f-a0b7-f8335b4e62a4
-- title:
--   Proof of Proposition 1, p. 35 — π₂(z^N, b) − π^N_2 > ∫_b^1 (2b − 2z^N) dF > 0 for z^N < b < 1
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ and $z^N$ the benchmark marginal consumer of Eq. (1). For data sharing on $[z^N,b]$ with uniform price $2b-1$ on $[b,1]$, firm 2's profit is $\pi_2(z^N,b)=\int_{z^N}^b(2x-1)\,dF(x)+(2b-1)(1-F(b))$. Then for every $b$ with $z^N<b<1$,
--   $$\pi_2(z^N,b)-\pi^N_2>\int_b^1(2b-2z^N)\,dF(x)>0.$$
--
--   This is the firm-2 half of Proposition 1: firm 2 keeps its customer base, charges personalized prices above the old uniform price on $[z^N,b]$, and a higher uniform price on $[b,1]$, so firm 2's participation constraint (IR) holds with strict slack.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 35, proof of Proposition 1

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem pi2_sub_piN2 {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    ∀ b ∈ Set.Ioo zN 1,
      (∫ x in b..1, (2 * b - 2 * zN) * f x) < pi2 F f zN b - piN2 F f zN ∧
        0 < ∫ x in b..1, (2 * b - 2 * zN) * f x := by sorry

end SoftenDataShare.Mutual
