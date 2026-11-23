-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_re_S
-- name    : ReciprocityTheory.ChartRestriction.G.I2.nA_re_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:29.248837+00:00
-- url     : https://prove2.me/theorems/7e72ef52-fdd3-4c36-a925-c62cfae22603
-- title:
--   I2: n A re S
-- statement:
--   The I2 construction uses the n A re S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaNA.lean#L95-L98

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

theorem ReciprocityTheory.ChartRestriction.G.I2.nA_re_S (q : ℕ) {n : ℕ} (v a : Fin n → Vsp X.dim) :
    ((q : ℂ) * Real.pi * HC v a + q * Real.pi * HC a a / 2).re =
      q * Real.pi * (HC v a).re + q * Real.pi * (HC a a).re / 2 := by sorry
