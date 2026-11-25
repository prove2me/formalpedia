-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_jj_mem
-- name    : ReciprocityTheory.ChartRestriction.G.I2.Col.jj_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:26:44.215492+00:00
-- url     : https://prove2.me/theorems/e4698bb2-e5af-4ad2-a5a6-7a1f990f236b
-- title:
--   Col: jj mem
-- statement:
--   The Col construction uses the jj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L200-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SecondProjectionOrthogonalComplement.lean#L200-L200

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))

theorem ReciprocityTheory.ChartRestriction.G.I2.Col.jj_mem (t : EuclideanSpace ℂ (Fin (gB K))) : jj K t ∈ V2 K := by sorry
