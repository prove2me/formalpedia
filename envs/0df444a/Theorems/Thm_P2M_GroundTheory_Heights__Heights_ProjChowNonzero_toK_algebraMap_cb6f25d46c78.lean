-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_algebraMap_cb6f25d46c78
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_algebraMap_cb6f25d46c78
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:28.138729+00:00
-- url     : https://prove2.me/theorems/6cdfe39d-7641-5357-b039-e4be4aa2d848
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K algebra Map cb6f25d46c78: P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K algebra Map cb6f25d46c78
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K algebra Map cb6f25d46c78 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero to K algebra Map cb6f25d46c78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L122-L125

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

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_algebraMap_cb6f25d46c78 (e : ℕ) (a : ℂ) :
    toK e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«toK_algebraMap» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_toK_algebraMap_cb6f25d46c78
