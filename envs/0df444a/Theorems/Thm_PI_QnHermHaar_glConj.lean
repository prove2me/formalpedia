-- Prove2me | Theorems.Thm_PI_QnHermHaar_glConj
-- name    : PI.QnHermHaar.glConj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:00:49.986606+00:00
-- url     : https://prove2.me/theorems/0ce176f7-af19-4b1a-b532-92ba1f17bf14
-- title:
--   Qn Herm Haar: gl Conj
-- statement:
--   The Qn Herm Haar construction uses the gl Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L35-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L35-L65

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

theorem PI.QnHermHaar.glConj {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hGl : GlRel E) (hQP : Q * P = 1) : GlRel (Econj E P Q) := by sorry
