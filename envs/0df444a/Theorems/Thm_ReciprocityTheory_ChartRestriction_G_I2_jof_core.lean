-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_core
-- name    : ReciprocityTheory.ChartRestriction.G.I2.jof_core
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:36.406547+00:00
-- url     : https://prove2.me/theorems/a7f355c6-0af6-51be-9572-b4f9a66a9c7a
-- title:
--   I2: jof core
-- statement:
--   The I2 construction uses the jof core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfNormLeTwo.lean#L39-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/HfNormLeTwo.lean#L39-L365

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfNormLeTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
variable {E : Type} [Field E] [NumberField E]
set_option maxHeartbeats 1000000
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.jof_core (hx : Ext.All) (hs : SplitStatement) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (he : ColEmptyStatement) [IsCMField E] (X : PT E) {n nb : ℕ}
    (bs : Fin nb → Block E n X.dim) (hD : Disj bs) (P : Par X (DF bs)) :
    ∃ F ∈ X.Sec P.q n, X.l2 P.q F = 1 ∧ P.Jbound n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2 := by sorry
