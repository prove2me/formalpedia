-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paMono_smul_paT
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paMono_smul_paT
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:45.230886+00:00
-- url     : https://prove2.me/theorems/51bcdb0c-2b1e-5c4b-b702-1b129244758b
-- title:
--   I2: pa Mono smul pa T
-- statement:
--   The I2 construction uses the pa Mono smul pa T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L28-L34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paMono_smul_paT (α : ι →₀ ℕ) (t : ℝ) (z : EuclideanSpace ℂ (Fin (Fintype.card ι))) :
    paMono α (t • paT z) = (t : ℂ) ^ α.degree *
      paMono (Finsupp.equivMapDomain (Fintype.equivFin ι) α) z := by sorry
