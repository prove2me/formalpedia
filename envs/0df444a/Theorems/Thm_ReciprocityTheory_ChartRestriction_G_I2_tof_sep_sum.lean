-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_sep_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_sep_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:51.09535+00:00
-- url     : https://prove2.me/theorems/aa666279-ff03-44f3-943a-777617134190
-- title:
--   I2: tof sep sum
-- statement:
--   The I2 construction uses the tof sep sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L143-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TofFinrankIRLe.lean#L143-L230

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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_sep_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I)
    (F : Finset (Vsp X.dim)) (hF : ∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) :
    ∑ y ∈ F, Real.exp (-(Real.pi / 2) * ‖u - y‖ ^ 2) ≤
      2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m := by sorry
