-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_ptNormOn_smul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.ptNormOn_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:10.239798+00:00
-- url     : https://prove2.me/theorems/7658bf60-89f4-4482-9293-3666b737172e
-- title:
--   Geo: pt Norm On smul
-- statement:
--   The Geo construction uses the pt Norm On smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L95-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.Geo.ptNormOn_smul {S : Set (ι → C)} (m : ConeMetricOn C ι S) (σ : o →+* C) {d : ℕ}
    {f : MvPolynomial ι o} (hf : (map σ f).IsHomogeneous d) {c : C} (hc : c ≠ 0) {z : ι → C}
    (hz : z ∈ S) (hcz : c • z ∈ S) : ptNormOn m σ d f (c • z) = ptNormOn m σ d f z := by sorry
