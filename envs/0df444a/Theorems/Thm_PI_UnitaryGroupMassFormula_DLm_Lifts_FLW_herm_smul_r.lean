-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_Lifts_FLW_herm_smul_r
-- name    : PI.UnitaryGroupMassFormula.DLm.Lifts.FLW.herm_smul_r
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:45.869865+00:00
-- url     : https://prove2.me/theorems/27b7d087-5c59-55dc-a8a2-032be41b6bee
-- title:
--   FLW: herm smul r
-- statement:
--   The FLW construction uses the herm smul r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean#L28-L30

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

theorem PI.UnitaryGroupMassFormula.DLm.Lifts.FLW.herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) :
    herm H u (c • w) = star c * herm H u w := by sorry
