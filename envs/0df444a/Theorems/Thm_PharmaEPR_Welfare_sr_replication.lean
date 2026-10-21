-- Prove2me | Theorems.Thm_PharmaEPR_Welfare_sr_replication
-- name    : PharmaEPR.Welfare.sr_replication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:33.805528+00:00
-- url     : https://prove2.me/theorems/762dee26-a4f1-4c04-b6f8-5f8384ab8c50
-- title:
--   Proof of Proposition 4, Online Appendix p. 4 — SR replicates an EC outcome
-- statement:
--   In the stated regime, suppose $u_p\ge\bar u_p^{SR}$ and $k<\bar k(u_p)$. For any feasible EC outcome at collection rate $r\in[0,1]$, an SR outcome exists at the same collection rate and fee $t=kr/2$, with equal total welfare:
--
--   $$r_{SR}=r_{EC}=r,\qquad t=\frac{kr}{2},\qquad
--   W^{SR}(r,t)=W^{EC}(r).$$
--
--   The SR fee exactly funds collection when the prescription is one unit, so the planner incurs no deficit. This claim supports the weak SR advantage in Table 2's high-health-benefit, low-collection-cost cell.
-- source:
--   Alev, Atasu, Toktay & Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020-09-05 posting), Online Appendix p. 4, proof of Proposition 4, third case

import Mathlib
import Definitions.Def_PharmaEPR_Welfare_Model

namespace PharmaEPR.Welfare

theorem sr_replication (P : Params) (hP : Regime P)
    (hu : uSR P ≤ P.up) (hk : P.k < kBar P) :
    ∀ r : ℝ, ∀ a : Action, Outcome P .EC ⟨r, 0⟩ a →
      ∃ a' : Action,
        Outcome P .SR ⟨r, P.k * r / 2⟩ a' ∧
        welfare P .SR ⟨r, P.k * r / 2⟩ a' =
          welfare P .EC ⟨r, 0⟩ a := by sorry

end PharmaEPR.Welfare
