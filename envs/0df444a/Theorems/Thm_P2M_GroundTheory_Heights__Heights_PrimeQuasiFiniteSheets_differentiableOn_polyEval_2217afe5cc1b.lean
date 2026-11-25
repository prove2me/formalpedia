-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_differentiableOn_polyEval_2217afe5cc1b
-- name    : P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_differentiableOn_polyEval_2217afe5cc1b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:25.191597+00:00
-- url     : https://prove2.me/theorems/47824e4a-15e9-4759-94df-5718e4d74eeb
-- title:
--   P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets differentiable On poly Eval 2217afe5cc1b: P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets differentiable On poly Eval 2217af
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets differentiable On poly Eval 2217afe5cc1b construction uses the P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets differentiable On poly Eval 2217afe5cc1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L52-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_differentiableOn_polyEval_2217afe5cc1b (P : Polynomial (MvPolynomial (Fin d) ℂ)) {ψ : (Fin d → ℂ) → ℂ}
    {U : Set (Fin d → ℂ)} (hψ : DifferentiableOn ℂ ψ U) :
    DifferentiableOn ℂ (fun w => (P.map (eval w)).eval (ψ w)) U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimeQuasiFiniteSheets».«differentiableOn_polyEval» := P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_differentiableOn_polyEval_2217afe5cc1b
