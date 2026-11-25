-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_invSelf_727517b3439f
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_invSelf_727517b3439f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:55.695748+00:00
-- url     : https://prove2.me/theorems/ed559528-3d04-4131-b04b-481413c50688
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt inv Self 727517b3439f: P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt inv Self 727517b3439f
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt inv Self 727517b3439f construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero at Pt inv Self 727517b3439f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L114-L120

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

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_invSelf_727517b3439f (e : ℕ) :
    atPt e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«atPt_invSelf» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_atPt_invSelf_727517b3439f
