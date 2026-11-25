-- Prove2me | Theorems.Thm_UpperTheory_GL_card_mul_delta_le_err
-- name    : UpperTheory.GL.card_mul_delta_le_err
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:09.143459+00:00
-- url     : https://prove2.me/theorems/910909f8-6f18-5a20-abb8-bf3ab0445a59
-- title:
--   GL: card mul delta le err
-- statement:
--   The GL construction uses the card mul delta le err property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/CostPropositionBasicBound.lean#L151-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ConductorsKronecker/CostPropositionBasicBound.lean#L151-L174

import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_CostPropositionBasicBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open UpperTheory UpperTheory.GL
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Deduction.CH

theorem UpperTheory.GL.card_mul_delta_le_err {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ)
    (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ)
    (hH : GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err) (hS : SmallCosts x ε (fPl H) b η θ Cd CL) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by sorry
