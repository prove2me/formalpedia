-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_part_A
-- name    : SolarNonOwn.BizChoice.part_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:15.989199+00:00
-- url     : https://prove2.me/theorems/2e39639c-7e14-4564-b7f3-6a9a814f32a9
-- title:
--   Proof of Proposition 1, part A summary, p. OA6 — optimum with p ≤ r
-- statement:
--   Restrict the company's price choice to PPA prices $p\le r$, while $0<c<C_0$. The proof's Case A1 candidate attains the regional maximum when $c\le C_{A1}$ and has positive PPA and sales adoption but no leasing. Case A2 attains it when $C_{A1}<c<C_{A2}$ and has positive adoption of all three models. Case A3 attains it when $c\ge C_{A2}$ and has positive PPA and leasing adoption but no sales. In each regime every regional maximizer has the stated offer set, and its profit equals the piecewise appendix value
--
--   $$\max_{s,l,p\le r}\Pi(s,l,p)=\Pi_A^*(c).$$
--
--   These three cases are the first half of the paper's global comparison.
--
--   **Formalization Note** The theorem uses adoption computed from customer choice, so it covers all prices in the stated region, including the boundary $p=r$.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. OA6 (PDF p. 38), proof of Proposition 1, part A summary; case formulas p. OA5

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

/-- Proof of Proposition 1, part A summary, p. OA6: the optimum with p ≤ r. -/
theorem part_A (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hh : h (Set.Iic 0) = 0) (hs : Standing prm) (c : ℝ)
    (hc : 0 < c) (hc0 : c < C0 prm) :
    (c ≤ CA1 prm →
      let x : Prices := ⟨sA1 prm c, lA1 prm c, prm.r⟩
      x.p ≤ prm.r ∧ IsMaxOn (profit prm h c) {y | y.p ≤ prm.r} x ∧
      profit prm h c x = profAstar prm c ∧
      ∀ y : Prices, y.p ≤ prm.r → IsMaxOn (profit prm h c) {z | z.p ≤ prm.r} y →
        offers prm h y = ({BizOpt.P, BizOpt.S} : Finset BizOpt)) ∧
    (CA1 prm < c → c < CA2 prm →
      let x : Prices := ⟨sA2 prm c, lA2 prm c, prm.r⟩
      x.p ≤ prm.r ∧ IsMaxOn (profit prm h c) {y | y.p ≤ prm.r} x ∧
      profit prm h c x = profAstar prm c ∧
      ∀ y : Prices, y.p ≤ prm.r → IsMaxOn (profit prm h c) {z | z.p ≤ prm.r} y →
        offers prm h y = ({BizOpt.P, BizOpt.L, BizOpt.S} : Finset BizOpt)) ∧
    (CA2 prm ≤ c →
      let x : Prices := ⟨sA3 prm, lA3 prm, prm.r⟩
      x.p ≤ prm.r ∧ IsMaxOn (profit prm h c) {y | y.p ≤ prm.r} x ∧
      profit prm h c x = profAstar prm c ∧
      ∀ y : Prices, y.p ≤ prm.r → IsMaxOn (profit prm h c) {z | z.p ≤ prm.r} y →
        offers prm h y = ({BizOpt.P, BizOpt.L} : Finset BizOpt)) := by sorry

end SolarNonOwn.BizChoice
