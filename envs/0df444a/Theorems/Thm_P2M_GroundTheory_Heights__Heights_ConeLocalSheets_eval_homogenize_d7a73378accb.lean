-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb
-- name    : P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:45.611263+00:00
-- url     : https://prove2.me/theorems/868745fe-4d51-495b-afc9-430b6ffb3162
-- title:
--   P2 M Ground Theory Heights  Heights Cone Local Sheets eval homogenize d7a73378accb: P2 M Ground Theory Heights  Heights Cone Local Sheets eval homogenize d7a73378accb
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Local Sheets eval homogenize d7a73378accb construction uses the P2 M Ground Theory Heights  Heights Cone Local Sheets eval homogenize d7a73378accb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLocalSheets.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb (c : MvPolynomial (Fin e) ℂ) (x : Fin e → ℂ) :
    eval (Fin.cons 1 x : Fin (e + 1) → ℂ) (homogenize c) = eval x c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeLocalSheets».«eval_homogenize» := P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eval_homogenize_d7a73378accb
