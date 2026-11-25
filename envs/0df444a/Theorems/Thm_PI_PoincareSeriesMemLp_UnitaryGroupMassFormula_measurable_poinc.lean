-- Prove2me | Theorems.Thm_PI_PoincareSeriesMemLp_UnitaryGroupMassFormula_measurable_poinc
-- name    : PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.measurable_poinc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:36:06.789713+00:00
-- url     : https://prove2.me/theorems/b52c4e65-76ab-47bb-84c2-2b3c00e5e3f9
-- title:
--   Unitary Group Mass Formula: measurable poinc
-- statement:
--   The Unitary Group Mass Formula construction uses the measurable poinc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PoincareSeriesMeasurability/FoldL2DoubleCoset.lean#L16-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PoincareSeriesMeasurability/FoldL2DoubleCoset.lean#L16-L32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldUnfold
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldMult
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoincareSeriesMeasurability_FoldL2DoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open PI PI.PoincareSeriesMemLp PI.PoincareSeriesMemLp.UnitaryGroupMassFormula
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

theorem PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.measurable_poinc {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (D : Set G) [Countable D] (Ph : G → ℂ) (hPh : Measurable Ph)
    (hs : ∀ x, (∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ) ≠ ⊤) : Measurable (poinc D Ph) := by sorry
