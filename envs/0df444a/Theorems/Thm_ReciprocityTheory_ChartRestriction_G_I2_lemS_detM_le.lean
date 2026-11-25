-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_detM_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.lemS_detM_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:09.914917+00:00
-- url     : https://prove2.me/theorems/5d8b968d-7f40-47dd-bdf0-37902e80abfd
-- title:
--   I2: lem S det M le
-- statement:
--   The I2 construction uses the lem S det M le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L117-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean#L117-L133

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
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
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.I2.lemS_detM_le (Y : GT ι) (b₀ : OrthonormalBasis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)) :
    |b₀.toBasis.det Y.b| ≤ 1 := by sorry
