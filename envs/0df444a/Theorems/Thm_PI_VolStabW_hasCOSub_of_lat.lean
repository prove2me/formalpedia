-- Prove2me | Theorems.Thm_PI_VolStabW_hasCOSub_of_lat
-- name    : PI.VolStabW.hasCOSub_of_lat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:46:32.920407+00:00
-- url     : https://prove2.me/theorems/e245a2b9-7f5e-4520-89d9-462a2fd6a9e1
-- title:
--   Vol Stab W: has COSub of lat
-- statement:
--   The Vol Stab W construction uses the has COSub of lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVNA.lean#L13-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVNA.lean#L13-L34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVNA
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct

theorem PI.VolStabW.hasCOSub_of_lat {𝕜 V : Type} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [TopologicalSpace V] [ContinuousSMul 𝕜 V] (L : AddSubgroup V)
    (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (π : 𝕜) (h0 : π ≠ 0)
    (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0)) : HasCOSub V := by sorry
