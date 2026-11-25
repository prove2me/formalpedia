-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_uMap_sep
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_uMap_sep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:35.224752+00:00
-- url     : https://prove2.me/theorems/4b5fb9a9-297a-5da9-8537-8d169bb61295
-- title:
--   I2: tof u Map sep
-- statement:
--   The I2 construction uses the tof u Map sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L114-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L114-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_uMap_sep [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {x x' : Vsp X.dim} (hx : x ∈ X.L) (hx' : x' ∈ X.L)
    (hne : uMap I x ≠ uMap I x') : 1 ≤ ‖uMap I x - uMap I x'‖ := by sorry
