-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_gauss_min_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.tof_gauss_min_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:30:43.946131+00:00
-- url     : https://prove2.me/theorems/4d4eff97-24be-4668-a49e-d22fcc9d5726
-- title:
--   I2: tof gauss min sum
-- statement:
--   The I2 construction uses the tof gauss min sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OneLeKappaMulPhase.lean#L177-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/OneLeKappaMulPhase.lean#L177-L209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofFinrankIRLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneLeKappaMulPhase
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

theorem ReciprocityTheory.ChartRestriction.G.I2.tof_gauss_min_sum [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (u : Vsp X.dim) (hu : u ∈ IR I) :
    ∃ y0 ∈ X.L, ∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
      ∑ y ∈ F, Real.exp (-Real.pi * ‖u - y‖ ^ 2) ≤
        2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m *
          Real.exp (-(Real.pi / 2) * ‖u - uMap I y0‖ ^ 2) := by sorry
