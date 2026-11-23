-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZetaWide_zeta__eq_af6bf53d4414
-- name    : P2M_GlobalTheory_ZetaWide_zeta__eq_af6bf53d4414
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:41.236945+00:00
-- url     : https://prove2.me/theorems/e6417500-df67-4bf1-adea-3c76a6350f37
-- title:
--   P2 M Global Theory Zeta Wide zeta  eq af6bf53d4414: P2 M Global Theory Zeta Wide zeta  eq af6bf53d4414
-- statement:
--   The P2 M Global Theory Zeta Wide zeta  eq af6bf53d4414 construction uses the P2 M Global Theory Zeta Wide zeta  eq af6bf53d4414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsMore.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsMore.lean#L76-L77

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

theorem P2M_GlobalTheory_ZetaWide_zeta__eq_af6bf53d4414 {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by sorry

alias «GlobalTheory».«ZetaWide».«zeta₁_eq» := P2M_GlobalTheory_ZetaWide_zeta__eq_af6bf53d4414
