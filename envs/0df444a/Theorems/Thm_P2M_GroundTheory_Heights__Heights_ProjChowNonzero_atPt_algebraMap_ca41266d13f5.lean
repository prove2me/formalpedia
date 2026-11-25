-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_algebraMap_ca41266d13f5
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_algebraMap_ca41266d13f5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:43.215211+00:00
-- url     : https://prove2.me/theorems/c4011676-2a3d-4f00-b275-d4c6c5fb3c8e
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt algebra Map ca41266d13f5: P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt algebra Map ca41266d13f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt algebra Map ca41266d13f5 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt algebra Map ca41266d13f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L127-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_algebraMap_ca41266d13f5 (e : ℕ) (a : ℂ) :
    atPt e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (AlgebraicClosure ℂ) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«atPt_algebraMap» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_algebraMap_ca41266d13f5
