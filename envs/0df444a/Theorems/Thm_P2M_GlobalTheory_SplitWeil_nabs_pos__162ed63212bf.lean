-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf
-- name    : P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:45.01861+00:00
-- url     : https://prove2.me/theorems/60be1577-3509-4700-b157-4691d246d19d
-- title:
--   P2 M Global Theory Split Weil nabs pos  162ed63212bf: P2 M Global Theory Split Weil nabs pos  162ed63212bf
-- statement:
--   The P2 M Global Theory Split Weil nabs pos  162ed63212bf construction uses the P2 M Global Theory Split Weil nabs pos  162ed63212bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LinearChangeOfVariablesLocalFieldMatrix.lean#L30-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]
omit [MeasurableSpace k] [BorelSpace k]

theorem P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf (x : kˣ) : 0 < nabs k x := by sorry

alias «GlobalTheory».«SplitWeil».«nabs_pos'» := P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf
