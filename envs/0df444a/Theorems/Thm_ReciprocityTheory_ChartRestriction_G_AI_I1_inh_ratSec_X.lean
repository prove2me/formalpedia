-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inh_ratSec_X
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inh_ratSec_X
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:35.003543+00:00
-- url     : https://prove2.me/theorems/ce8732e1-0c51-46ee-a403-a55a8f396183
-- title:
--   I1: inh rat Sec X
-- statement:
--   The I1 construction uses the inh rat Sec X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/Inhabit.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/Inhabit.lean#L50-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_Inhabit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] [DecidableEq (Σ k, ι k)]
  {F : Type*} [Field F]
variable [DecidableEq K]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inh_ratSec_X (V : Ideal (MRingOver F ι)) (p : Σ k, ι k) (hp : (X p : MRingOver F ι) ∉ V)
    (hV : (1 : MRingOver F ι) ∉ V) : IsRatSection V (Pi.single p.1 1) (X p) 1 := by sorry
