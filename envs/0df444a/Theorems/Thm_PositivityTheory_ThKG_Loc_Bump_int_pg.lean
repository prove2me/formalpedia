-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_int_pg
-- name    : PositivityTheory.ThKG.Loc.Bump.int_pg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:11.002034+00:00
-- url     : https://prove2.me/theorems/b7abeb87-6291-4aec-92cf-0ccbbd8f0afe
-- title:
--   Bump: int pg
-- statement:
--   The Bump construction uses the int pg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L143-L148

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.int_pg {g : ℂ → ℂ} (hg : Measurable g) (s : ℕ) (h : ∀ z, ‖g z‖ ≤ ‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2)) : Integrable g := by sorry
