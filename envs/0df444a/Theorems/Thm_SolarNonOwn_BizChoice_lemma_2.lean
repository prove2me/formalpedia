-- Prove2me | Theorems.Thm_SolarNonOwn_BizChoice_lemma_2
-- name    : SolarNonOwn.BizChoice.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:49.962895+00:00
-- url     : https://prove2.me/theorems/7ab001ed-153e-4b2e-af6a-bbaddbb9381a
-- title:
--   Lemma 2, p. 14 — customer segmentation by expected generation
-- statement:
--   Fix prices $s,l,p$ and let $\eta$ be a customer's expected generation. Write $\eta_1=((1-\alpha)s-l)/\beta$, $\eta_2=l/p$ and $\eta_3=l/r$. If $0<p\le r$ and $0\le\eta_2\le\eta_1\le g$, customers above $\eta_1$ choose sales, those strictly between $\eta_2$ and $\eta_1$ choose leasing, and those strictly below $\eta_2$ choose PPA. Their respective population shares are
--
--   $$N^S=1-\frac{\eta_1}{g},\qquad N^L=\frac{\eta_1-\eta_2}{g},\qquad N^P=\frac{\eta_2}{g}.$$
--
--   If $p>r$ and $0\le\eta_3\le\eta_1\le g$, the high and middle groups still choose sales and leasing, while the low group relies on the utility. In this case $N^S=1-\eta_1/g$, $N^L=(\eta_1-\eta_3)/g$, and $N^P=0$. These regions turn customer choices into the adoption levels in the company's profit.
--
--   **Formalization Note** The theorem states open intervals at ties. The additional $p>0$ condition in the first case gives the proof's expression $l/p$ its intended meaning. The interval ordering expresses the paper's nonnegative-adoption feasibility condition. The parameters satisfy only the §3 model assumptions $\alpha,\beta>0$, $0<t<r$, $g>0$; the later conditions $\beta<r$ and $\alpha<A$ of p. 15 are not assumed.
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), p. 14, Lemma 2; p. OA4, thresholds

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

/-- Lemma 2, p. 14, and its thresholds from p. OA4. Endpoint choices are fixed by
`choice`; the stated open intervals and aggregate shares are independent of those ties. -/
theorem lemma_2 (prm : Params) (h : Measure ℝ) [IsProbabilityMeasure h]
    (hh : h (Set.Iic 0) = 0) (hs : ModelAssumptions prm) (x : Prices) :
    (0 < x.p → x.p ≤ prm.r →
      0 ≤ eta2 x.l x.p → eta2 x.l x.p ≤ eta1 prm x.s x.l →
      eta1 prm x.s x.l ≤ prm.g →
      (∀ η d : ℝ, eta1 prm x.s x.l < η → η ≤ prm.g → choice prm x η d = .S) ∧
      (∀ η d : ℝ, eta2 x.l x.p < η → η < eta1 prm x.s x.l → choice prm x η d = .L) ∧
      (∀ η d : ℝ, 0 < η → η < eta2 x.l x.p → choice prm x η d = .P) ∧
      adoption prm h x .S = 1 - eta1 prm x.s x.l / prm.g ∧
      adoption prm h x .L = (eta1 prm x.s x.l - eta2 x.l x.p) / prm.g ∧
      adoption prm h x .P = eta2 x.l x.p / prm.g) ∧
    (prm.r < x.p →
      0 ≤ eta3 prm x.l → eta3 prm x.l ≤ eta1 prm x.s x.l →
      eta1 prm x.s x.l ≤ prm.g →
      (∀ η d : ℝ, eta1 prm x.s x.l < η → η ≤ prm.g → choice prm x η d = .S) ∧
      (∀ η d : ℝ, eta3 prm x.l < η → η < eta1 prm x.s x.l → choice prm x η d = .L) ∧
      (∀ η d : ℝ, 0 < η → η < eta3 prm x.l → choice prm x η d = .U) ∧
      adoption prm h x .S = 1 - eta1 prm x.s x.l / prm.g ∧
      adoption prm h x .L = (eta1 prm x.s x.l - eta3 prm x.l) / prm.g ∧
      adoption prm h x .P = 0) := by sorry

end SolarNonOwn.BizChoice
