-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_invSelf_f00771d14dee
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_invSelf_f00771d14dee
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:23.47808+00:00
-- url     : https://prove2.me/theorems/46c1099b-6a9c-4056-bf7e-18c219f303ea
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K inv Self f00771d14dee: P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K inv Self f00771d14dee
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K inv Self f00771d14dee construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K inv Self f00771d14dee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L108-L112

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

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_invSelf_f00771d14dee (e : ℕ) :
    toK e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = (projVar e 0)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«toK_invSelf» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_invSelf_f00771d14dee
