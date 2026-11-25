-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_eval_pullback_877f341acccc
-- name    : P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_eval_pullback_877f341acccc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:09.304268+00:00
-- url     : https://prove2.me/theorems/47fb9514-9dd9-4c44-a1a9-7d7c3acf6ba2
-- title:
--   P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets eval pullback 877f341acccc: P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets eval pullback 877f341acccc
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets eval pullback 877f341acccc construction uses the P2 M Ground Theory Heights  Heights Prime Quasi Finite Sheets eval pullback 877f341acccc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimeQuasiFiniteSheets.lean#L18-L26

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

theorem P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_eval_pullback_877f341acccc (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (g : MvPolynomial (Fin d) ℂ) :
    eval x (ComplexSets.pullback A g) = eval (A.mulVec x) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimeQuasiFiniteSheets».«eval_pullback» := P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_eval_pullback_877f341acccc
