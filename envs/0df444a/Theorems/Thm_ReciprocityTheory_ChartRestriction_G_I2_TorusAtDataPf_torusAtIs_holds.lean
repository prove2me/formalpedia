-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_torusAtIs_holds
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.torusAtIs_holds
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:44.807049+00:00
-- url     : https://prove2.me/theorems/566cbc93-8c8f-4ed2-a92f-ea3a99c9c34f
-- title:
--   Torus At Data Pf: torus At Is holds
-- statement:
--   The Torus At Data Pf construction uses the torus At Is holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPf.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPf.lean#L113-L115

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.torusAtIs_holds : TorusAtIsStatement := by sorry
