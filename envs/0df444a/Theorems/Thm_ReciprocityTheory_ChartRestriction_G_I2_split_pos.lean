-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_split_pos
-- name    : ReciprocityTheory.ChartRestriction.G.I2.split_pos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:31:57.88632+00:00
-- url     : https://prove2.me/theorems/50268fea-a278-46ea-b1cd-b421949991da
-- title:
--   I2: split pos
-- statement:
--   The I2 construction uses the split pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitG.lean#L109-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitG.lean#L109-L211

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitG
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
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.I2.split_pos (X : PT E) {DF : ℕ} (P : Par X DF) (h : X.la1 < P.th) : ∃ I, IsSplit P I := by sorry
