-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirst_C_mul_fda7cfa4cf95
-- name    : P2M_GroundTheory_Heights__Heights_specFirst_C_mul_fda7cfa4cf95
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:03.503051+00:00
-- url     : https://prove2.me/theorems/bf0ec250-4fdd-5e08-b700-5987045284c3
-- title:
--   P2 M Ground Theory Heights  Heights spec First C mul fda7cfa4cf95: P2 M Ground Theory Heights  Heights spec First C mul fda7cfa4cf95
-- statement:
--   The P2 M Ground Theory Heights  Heights spec First C mul fda7cfa4cf95 construction uses the P2 M Ground Theory Heights  Heights spec First C mul fda7cfa4cf95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSpecFirstSwapMahler.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSpecFirstSwapMahler.lean#L20-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSpecFirstSwapMahler
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

theorem P2M_GroundTheory_Heights__Heights_specFirst_C_mul_fda7cfa4cf95 {n k : ℕ} (c : ℂ) (f : MvPolynomial (Fin (k + 1) × Fin n) ℂ) (u : Fin n → ℂ) :
    specFirst (C c * f) u = C c * specFirst f u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«specFirst_C_mul» := P2M_GroundTheory_Heights__Heights_specFirst_C_mul_fda7cfa4cf95
