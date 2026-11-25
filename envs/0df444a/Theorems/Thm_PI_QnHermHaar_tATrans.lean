-- Prove2me | Theorems.Thm_PI_QnHermHaar_tATrans
-- name    : PI.QnHermHaar.tATrans
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:05.904133+00:00
-- url     : https://prove2.me/theorems/20b1a0bc-7065-5091-b0c0-d41dd1e6c491
-- title:
--   Qn Herm Haar: t ATrans
-- statement:
--   The Qn Herm Haar construction uses the t ATrans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L161-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L161-L204

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
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

theorem PI.QnHermHaar.tATrans (hCC : ContractionsCovariant) {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (P Q : Matrix (Fin m) (Fin m) ℂ)
    (hGl : GlRel E) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (p q : Fin 2) :
    tA E Y Yb x xb u p q = tA (Econj E P Q) (vecC Q Y) (covC P Yb) (Q *ᵥ x) (xb ᵥ* P) u p q := by sorry
