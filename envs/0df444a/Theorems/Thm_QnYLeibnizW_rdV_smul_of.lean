-- Prove2me | Theorems.Thm_QnYLeibnizW_rdV_smul_of
-- name    : QnYLeibnizW.rdV_smul_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:31:43.192296+00:00
-- url     : https://prove2.me/theorems/1190bdc4-3bdd-42a8-b1a1-8add32d61191
-- title:
--   Qn YLeibniz W: rd V smul of
-- statement:
--   The Qn YLeibniz W construction uses the rd V smul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateTransposeLeibniz/YOperatorLeibnizRule.lean#L45-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem QnYLeibnizW.rdV_smul_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X g : Matrix (Fin n) (Fin n) ℂ) (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (d : ℂ) (L : E)
    (hφ : HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) d 0)
    (hf : HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) L 0) :
    RdV X (fun x => φ x • f x) g = φ g • L + d • f g := by sorry
