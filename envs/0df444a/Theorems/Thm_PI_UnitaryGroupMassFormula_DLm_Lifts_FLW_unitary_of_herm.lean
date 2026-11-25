-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_Lifts_FLW_unitary_of_herm
-- name    : PI.UnitaryGroupMassFormula.DLm.Lifts.FLW.unitary_of_herm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:49:00.066164+00:00
-- url     : https://prove2.me/theorems/11161ab2-f577-50c6-9704-dd44c9cafd54
-- title:
--   FLW: unitary of herm
-- statement:
--   The FLW construction uses the unitary of herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean#L32-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFlWitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Lifts
open PI.UnitaryGroupMassFormula.DLm.Lifts.FLW
variable {n : ℕ}

theorem PI.UnitaryGroupMassFormula.DLm.Lifts.FLW.unitary_of_herm (H M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ u v, herm H (M *ᵥ u) (M *ᵥ v) = herm H u v) :
    Mᴴ * H * M = H := by sorry
