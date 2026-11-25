-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaLocal_order_zeta__e3d6133bc940
-- name    : P2M_GlobalTheory_ZetaLocal_order_zeta__e3d6133bc940
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:23.817082+00:00
-- url     : https://prove2.me/theorems/eedca16d-10c7-4285-8d6e-3ba9cd99a1ab
-- title:
--   P2 M Global Theory Zeta Local order zeta  e3d6133bc940: P2 M Global Theory Zeta Local order zeta  e3d6133bc940
-- statement:
--   The P2 M Global Theory Zeta Local order zeta  e3d6133bc940 construction uses the P2 M Global Theory Zeta Local order zeta  e3d6133bc940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSum.lean#L17-L26

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

theorem P2M_GlobalTheory_ZetaLocal_order_zeta__e3d6133bc940 {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by sorry

alias «GlobalTheory».«ZetaLocal».«order_zeta₁» := P2M_GlobalTheory_ZetaLocal_order_zeta__e3d6133bc940
