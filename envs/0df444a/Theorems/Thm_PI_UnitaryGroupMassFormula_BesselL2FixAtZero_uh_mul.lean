-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BesselL2FixAtZero_uh_mul
-- name    : PI.UnitaryGroupMassFormula.BesselL2FixAtZero.uh_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:43:52.350804+00:00
-- url     : https://prove2.me/theorems/e3e8c4f0-1eac-5f39-9a43-54adcbfbfc15
-- title:
--   Bessel L2 Fix At Zero: uh mul
-- statement:
--   The Bessel L2 Fix At Zero construction uses the uh mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SigmaMul.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BesselSquareIntegrable/SigmaMul.lean#L44-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselL2FixAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SigmaMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BesselL2FixAtZero
open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep PI.BesselL2FixAtZero

theorem PI.UnitaryGroupMassFormula.BesselL2FixAtZero.uh_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by sorry
