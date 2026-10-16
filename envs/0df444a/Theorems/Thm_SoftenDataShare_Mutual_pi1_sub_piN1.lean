-- Prove2me | Theorems.Thm_SoftenDataShare_Mutual_pi1_sub_piN1
-- name    : SoftenDataShare.Mutual.pi1_sub_piN1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:55.243301+00:00
-- url     : https://prove2.me/theorems/6ca7e07e-e649-4681-9eb3-eacff0196538
-- title:
--   Proof of Proposition 1, p. 35 — π₁(z^N, b) − π^N_1 = 2(b − z^N)F(z^N), positive for b > z^N
-- statement:
--   Let $(F,f)$ be a monotone-hazard-rate distribution on $[0,1]$ and $z^N$ the benchmark marginal consumer of Eq. (1). For data sharing on $[z^N,b]$, firm 1's profit is $\pi_1(z^N,b)=\int_0^{z^N}\bigl((2b-1)+(1-2x)\bigr)\,dF(x)$. Then for every real $b$,
--   $$\pi_1(z^N,b)-\pi^N_1=2\,(b-z^N)\,F(z^N),$$
--   and this difference is strictly positive whenever $b>z^N$.
--
--   Sharing data on firm 2's customer base $[z^N,b]$ costs firm 1 no market share, and raises the price it can charge each of its consumers by $2(b-z^N)$; this identity is the firm-1 half of Proposition 1.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), p. 35, proof of Proposition 1

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist
import Definitions.Def_SoftenDataShare_Mutual_Model

namespace SoftenDataShare.Mutual

theorem pi1_sub_piN1 {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f)
    (hzN : IsZN F f zN) :
    (∀ b : ℝ, pi1 f zN b - piN1 F f zN = 2 * (b - zN) * F zN) ∧
      ∀ b : ℝ, zN < b → 0 < pi1 f zN b - piN1 F f zN := by sorry

end SoftenDataShare.Mutual
