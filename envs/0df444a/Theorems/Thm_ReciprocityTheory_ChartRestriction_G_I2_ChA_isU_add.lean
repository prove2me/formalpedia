-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_isU_add
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ChA.isU_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:57.290438+00:00
-- url     : https://prove2.me/theorems/660e0e1a-b0ef-5123-abf8-a1063b181fdc
-- title:
--   Ch A: is U add
-- statement:
--   The Ch A construction uses the is U add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfRsmulRight.lean#L113-L116

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA

theorem ReciprocityTheory.ChartRestriction.G.I2.ChA.isU_add {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim}
    (hu : IsU I x u) (hv : IsU I y v) : IsU I (x + y) (u + v) := by sorry
