-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_re_U
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_re_U
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:07.883283+00:00
-- url     : https://prove2.me/theorems/24fc694d-55b0-4f40-9bf6-e6cfdeac07ec
-- title:
--   I2: n A re U
-- statement:
--   The I2 construction uses the n A re U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L90-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_re_U (q : ℕ) {n : ℕ} (v a : Fin n → Vsp X.dim) :
    ((q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2).re =
      q * Real.pi * (HC v a).re - q * Real.pi * (HC a a).re / 2 := by sorry
