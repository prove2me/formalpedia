-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaLocal_norm_zeta__le_8dd564b5075f
-- name    : P2M_GlobalTheory_ZetaLocal_norm_zeta__le_8dd564b5075f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:44.598183+00:00
-- url     : https://prove2.me/theorems/14d97e58-5d66-4d39-885b-0a100742dd29
-- title:
--   P2 M Global Theory Zeta Local norm zeta  le 8dd564b5075f: P2 M Global Theory Zeta Local norm zeta  le 8dd564b5075f
-- statement:
--   The P2 M Global Theory Zeta Local norm zeta  le 8dd564b5075f construction uses the P2 M Global Theory Zeta Local norm zeta  le 8dd564b5075f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L43-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L43-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaLocal

theorem P2M_GlobalTheory_ZetaLocal_norm_zeta__le_8dd564b5075f (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta₁ (3/2 + t * I + z)‖ ≤ 5 * (|t| + 2) ^ 2 := by sorry

alias «GlobalTheory».«ZetaLocal».«norm_zeta₁_le» := P2M_GlobalTheory_ZetaLocal_norm_zeta__le_8dd564b5075f
