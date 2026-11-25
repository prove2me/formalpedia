-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_of_isHomogeneousP
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isHomogeneousP
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:15.963846+00:00
-- url     : https://prove2.me/theorems/4aeea32a-1381-5599-8014-bb67672944d2
-- title:
--   Geo: eval smul of is Homogeneous P
-- statement:
--   The Geo construction uses the eval smul of is Homogeneous P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L83-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenMet.lean#L83-L93

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_of_isHomogeneousP {R : Type*} [CommRing R] {φ : MvPolynomial ι R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : ι → R) : eval (c • z) φ = c ^ d * eval z φ := by sorry
