-- Prove2me | Theorems.Thm_PI_QnHermHaar_diagInvol
-- name    : PI.QnHermHaar.diagInvol
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:48.286667+00:00
-- url     : https://prove2.me/theorems/cd6a67ea-c580-50ab-93d6-fb2c0ebd191f
-- title:
--   Qn Herm Haar: diag Invol
-- statement:
--   The Qn Herm Haar construction uses the diag Invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L169-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L169-L208

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.diagInvol {m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (hH : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ), star U * U = 1 ∧ U * star U = 1 ∧
      Hm * U = U * diagonal (fun j => ((ε j : ℤ) : ℂ)) := by sorry
