-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_Lifts_wittHpk
-- name    : PI.UnitaryGroupMassFormula.DLm.Lifts.wittHpk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:56:27.215573+00:00
-- url     : https://prove2.me/theorems/dfa7effa-1c24-4cd2-904f-2789cac5bf13
-- title:
--   Lifts: witt Hpk
-- statement:
--   The Lifts construction uses the witt Hpk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean#L46-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFlWitt.lean#L46-L125

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

theorem PI.UnitaryGroupMassFormula.DLm.Lifts.wittHpk (k r : ℕ) {ι : Type} [Fintype ι] (x y : ι → Fin (2 * r + k + 1) → ℂ)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hg : ∀ i j, herm (Hpk k r) (x i) (x j) = herm (Hpk k r) (y i) (y j)) :
    ∃ g ∈ B.GV k r, ∀ i, g *ᵥ x i = y i := by sorry
