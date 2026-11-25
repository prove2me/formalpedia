-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_aeval_tan
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.aeval_tan
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:16.510472+00:00
-- url     : https://prove2.me/theorems/797b3e63-fcb1-5b35-86f4-08070acb7e94
-- title:
--   Eig D: aeval tan
-- statement:
--   The Eig D construction uses the aeval tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SingleMemDegLE.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SingleMemDegLE.lean#L17-L34

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.aeval_tan {ι : Type} [DecidableEq ι] (ℓ : ι) (P : MvPolynomial ι V) :
    aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) P =
      algebraMap V (DualNumber V) (constantCoeff P) + coeff (Finsupp.single ℓ 1) P • DualNumber.eps := by sorry
