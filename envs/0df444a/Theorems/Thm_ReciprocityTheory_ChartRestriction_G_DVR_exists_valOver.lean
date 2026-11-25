-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_valOver
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:16.211332+00:00
-- url     : https://prove2.me/theorems/492a2f73-0509-4c80-af4c-1e6fe458cf03
-- title:
--   DVR: exists val Over
-- statement:
--   The DVR construction uses the exists val Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValExt.lean#L9-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValExt.lean#L9-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F] [Algebra (FractionRing V) F]
    [Algebra.IsAlgebraic (FractionRing V) F] : ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by sorry
