-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_supNormOn_restrict
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.supNormOn_restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:53.246884+00:00
-- url     : https://prove2.me/theorems/adc3fa9a-96fb-5304-b231-a7e4851ef0da
-- title:
--   Geo: sup Norm On restrict
-- statement:
--   The Geo construction uses the sup Norm On restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L52-L55

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
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.Geo.supNormOn_restrict (m : ConeMetric C ι) (σ : o →+* C) (I : Ideal (MvPolynomial ι o))
    (d : ℕ) (f : MvPolynomial ι o) :
    supNormOn (m.restrict (conePts σ I) (conePts_ne_zero σ I)) σ d f = supNorm m σ I d f := by sorry
