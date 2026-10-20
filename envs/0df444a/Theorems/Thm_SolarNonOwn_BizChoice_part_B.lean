-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_part_B
-- name    : SolarNonOwn.BizChoice.part_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:21.52933+00:00
-- url     : https://prove2.me/theorems/5880f45b-a4b9-467d-b744-9dfe7550cea8
-- title:
--   Proof of Proposition 1, part B summary, p. OA7 — optimum with p > r
-- statement:
--   Restrict the company to PPA prices $p>r$ and panel costs $0<c<C_0$. If $\alpha<A_2=\beta/(\beta+r)$, Case B2 attains the regional maximum and offers sales and leasing. If $A_2\le\alpha$, Case B1 attains the regional maximum and offers sales only. In both cases PPA adoption is zero, every regional maximizer has the indicated offer set, and
--
--   $$\max_{s,l,p>r}\Pi(s,l,p)=\Pi_B^*(c).$$
--
--   This identifies the best profit without PPA adoption for comparison with part A.
--
--   **Formalization Note** The exhibited candidates use $p=r+1$; the PPA price is immaterial in this region because customers do not choose PPA.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. OA7 (PDF p. 39), proof of Proposition 1, part B summary; case formulas p. OA6

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

/-- Proof of Proposition 1, part B summary, p. OA7: the optimum with p > r. -/
theorem part_B (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hh : h (Set.Iic 0) = 0) (hs : Standing prm) (c : ℝ)
    (hc : 0 < c) (hc0 : c < C0 prm) :
    (prm.alpha < A2 prm →
      let x : Prices := ⟨sB2 prm c, lB2 prm c, prm.r + 1⟩
      prm.r < x.p ∧ IsMaxOn (profit prm h c) {y | prm.r < y.p} x ∧
      profit prm h c x = profBstar prm c ∧
      ∀ y : Prices, prm.r < y.p → IsMaxOn (profit prm h c) {z | prm.r < z.p} y →
        offers prm h y = ({BizOpt.L, BizOpt.S} : Finset BizOpt)) ∧
    (A2 prm ≤ prm.alpha →
      let x : Prices := ⟨sB1 prm c, lB1 prm c, prm.r + 1⟩
      prm.r < x.p ∧ IsMaxOn (profit prm h c) {y | prm.r < y.p} x ∧
      profit prm h c x = profBstar prm c ∧
      ∀ y : Prices, prm.r < y.p → IsMaxOn (profit prm h c) {z | prm.r < z.p} y →
        offers prm h y = ({BizOpt.S} : Finset BizOpt)) := by sorry

end SolarNonOwn.BizChoice
