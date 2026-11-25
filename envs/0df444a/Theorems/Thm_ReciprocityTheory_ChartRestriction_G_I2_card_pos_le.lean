-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_card_pos_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.card_pos_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:44.977948+00:00
-- url     : https://prove2.me/theorems/50a6d467-3a5a-5edc-bd7d-f2ed202bf6f6
-- title:
--   I2: card pos le
-- statement:
--   The I2 construction uses the card pos le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardChoiceLe.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardChoiceLe.lean#L39-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IteratedDerivListBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneAddPowSubOneLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

theorem ReciprocityTheory.ChartRestriction.G.I2.card_pos_le : Fintype.card (Σ j : Fin nb, Fin (bs j).i) ≤ DF bs := by sorry
