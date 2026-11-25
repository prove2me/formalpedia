-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaWide_order_zeta__eq_8b737bca923c
-- name    : P2M_GlobalTheory_ZetaWide_order_zeta__eq_8b737bca923c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:50.646866+00:00
-- url     : https://prove2.me/theorems/26127fd8-52b1-4ad1-8792-d598da998303
-- title:
--   P2 M Global Theory Zeta Wide order zeta  eq 8b737bca923c: P2 M Global Theory Zeta Wide order zeta  eq 8b737bca923c
-- statement:
--   The P2 M Global Theory Zeta Wide order zeta  eq 8b737bca923c construction uses the P2 M Global Theory Zeta Wide order zeta  eq 8b737bca923c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsMore.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsMore.lean#L79-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaWide

theorem P2M_GlobalTheory_ZetaWide_order_zeta__eq_8b737bca923c {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt riemannZeta₁ s = analyticOrderNatAt riemannZeta s := by sorry

alias «GlobalTheory».«ZetaWide».«order_zeta₁_eq» := P2M_GlobalTheory_ZetaWide_order_zeta__eq_8b737bca923c
