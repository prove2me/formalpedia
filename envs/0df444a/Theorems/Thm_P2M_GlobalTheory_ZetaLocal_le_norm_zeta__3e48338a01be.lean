-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaLocal_le_norm_zeta__3e48338a01be
-- name    : P2M_GlobalTheory_ZetaLocal_le_norm_zeta__3e48338a01be
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:54.285068+00:00
-- url     : https://prove2.me/theorems/c683037a-778e-4a9b-afd3-3c9003947feb
-- title:
--   P2 M Global Theory Zeta Local le norm zeta  3e48338a01be: P2 M Global Theory Zeta Local le norm zeta  3e48338a01be
-- statement:
--   The P2 M Global Theory Zeta Local le norm zeta  3e48338a01be construction uses the P2 M Global Theory Zeta Local le norm zeta  3e48338a01be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L74-L85

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

theorem P2M_GlobalTheory_ZetaLocal_le_norm_zeta__3e48338a01be (t : ℝ) : 1 / 6 ≤ ‖riemannZeta₁ (3/2 + t * I)‖ := by sorry

alias «GlobalTheory».«ZetaLocal».«le_norm_zeta₁» := P2M_GlobalTheory_ZetaLocal_le_norm_zeta__3e48338a01be
