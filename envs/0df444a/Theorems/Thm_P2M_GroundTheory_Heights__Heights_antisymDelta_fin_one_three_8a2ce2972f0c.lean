-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymDelta_fin_one_three_8a2ce2972f0c
-- name    : P2M_GroundTheory_Heights__Heights_antisymDelta_fin_one_three_8a2ce2972f0c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:09.177585+00:00
-- url     : https://prove2.me/theorems/0f68fea2-9826-4dfc-acdf-35f272edef35
-- title:
--   P2 M Ground Theory Heights  Heights antisym Delta fin one three 8a2ce2972f0c: P2 M Ground Theory Heights  Heights antisym Delta fin one three 8a2ce2972f0c
-- statement:
--   The P2 M Ground Theory Heights  Heights antisym Delta fin one three 8a2ce2972f0c construction uses the P2 M Ground Theory Heights  Heights antisym Delta fin one three 8a2ce2972f0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/Statements.lean#L126-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
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

theorem P2M_GroundTheory_Heights__Heights_antisymDelta_fin_one_three_8a2ce2972f0c :
    antisymDelta (Fin 1) 3 = (X (0, 0) - X (0, 1)) * (X (0, 0) - X (0, 2)) * (X (0, 1) - X (0, 2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«antisymDelta_fin_one_three» := P2M_GroundTheory_Heights__Heights_antisymDelta_fin_one_three_8a2ce2972f0c
