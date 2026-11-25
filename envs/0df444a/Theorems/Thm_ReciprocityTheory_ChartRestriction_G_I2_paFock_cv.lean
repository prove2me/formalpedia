-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paFock_cv
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paFock_cv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:13.961504+00:00
-- url     : https://prove2.me/theorems/1da957ef-3166-59d0-b512-ed88d5740e5d
-- title:
--   I2: pa Fock cv
-- statement:
--   The I2 construction uses the pa Fock cv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L67-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L67-L105

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

theorem ReciprocityTheory.ChartRestriction.G.I2.paFock_cv {q : ℕ} (hq : 1 ≤ q) (H K : EuclideanSpace ℂ ι → ℂ) :
    fockIP (fun z => H ((Real.sqrt (q * Real.pi))⁻¹ • paT z))
      (fun z => K ((Real.sqrt (q * Real.pi))⁻¹ • paT z)) = (q : ℂ) ^ Fintype.card ι * paIP q H K := by sorry
