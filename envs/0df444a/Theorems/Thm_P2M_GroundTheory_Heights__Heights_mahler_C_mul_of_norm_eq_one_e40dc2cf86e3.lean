-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_mul_of_norm_eq_one_e40dc2cf86e3
-- name    : P2M_GroundTheory_Heights__Heights_mahler_C_mul_of_norm_eq_one_e40dc2cf86e3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:46.480563+00:00
-- url     : https://prove2.me/theorems/ec8093ea-fb5a-4f3e-b74c-dd2860b774c8
-- title:
--   P2 M Ground Theory Heights  Heights mahler C mul of norm eq one e40dc2cf86e3: P2 M Ground Theory Heights  Heights mahler C mul of norm eq one e40dc2cf86e3
-- statement:
--   The P2 M Ground Theory Heights  Heights mahler C mul of norm eq one e40dc2cf86e3 construction uses the P2 M Ground Theory Heights  Heights mahler C mul of norm eq one e40dc2cf86e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSpecFirstSwapMahler.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSpecFirstSwapMahler.lean#L11-L18

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

theorem P2M_GroundTheory_Heights__Heights_mahler_C_mul_of_norm_eq_one_e40dc2cf86e3 {n k : ℕ} (h : HermNorm n) (c : ℂ) (hc : ‖c‖ = 1)
    (g : MvPolynomial (Fin k × Fin n) ℂ) : mahler h k (C c * g) = mahler h k g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mahler_C_mul_of_norm_eq_one» := P2M_GroundTheory_Heights__Heights_mahler_C_mul_of_norm_eq_one_e40dc2cf86e3
