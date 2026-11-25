-- Prove2me | Theorems.Thm_PI_VolStabW_um_sigmaCompact_HA
-- name    : PI.VolStabW.um_sigmaCompact_HA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:47.03775+00:00
-- url     : https://prove2.me/theorems/62923d62-81e4-453a-804c-b2ddd6f32816
-- title:
--   Vol Stab W: um sigma Compact HA
-- statement:
--   The Vol Stab W construction uses the um sigma Compact HA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/Unimod.lean#L214-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/Unimod.lean#L214-L222

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem PI.VolStabW.um_sigmaCompact_HA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (h : SWa1 F E σ M J) : SigmaCompactSpace (HA (AF F) σ J) := by sorry
