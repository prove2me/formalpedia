-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_colL_cons
-- name    : ReciprocityTheory.ChartRestriction.G.I2.colL_cons
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:36.156454+00:00
-- url     : https://prove2.me/theorems/4e50d2d3-f5ea-4c34-b0c2-5f3ef4d13310
-- title:
--   I2: col L cons
-- statement:
--   The I2 construction uses the col L cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L72-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.colL_cons {n : ℕ} (a : Fin n × W) (L : List (Fin n × W)) (k : Fin n) :
    colL (a :: L) k = if a.1 = k then a.2 :: colL L k else colL L k := by sorry
