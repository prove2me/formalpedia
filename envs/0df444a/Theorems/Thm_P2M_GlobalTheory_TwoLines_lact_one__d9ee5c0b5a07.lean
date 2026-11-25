-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TwoLines_lact_one__d9ee5c0b5a07
-- name    : P2M_GlobalTheory_TwoLines_lact_one__d9ee5c0b5a07
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:13.277321+00:00
-- url     : https://prove2.me/theorems/c17b90ed-cded-580d-8d14-d72961ddcb15
-- title:
--   P2 M Global Theory Two Lines lact one  d9ee5c0b5a07: P2 M Global Theory Two Lines lact one  d9ee5c0b5a07
-- statement:
--   The P2 M Global Theory Two Lines lact one  d9ee5c0b5a07 construction uses the P2 M Global Theory Two Lines lact one  d9ee5c0b5a07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean#L65-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem P2M_GlobalTheory_TwoLines_lact_one__d9ee5c0b5a07 {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) : lact (1 : GL (Fin 2) E) x = x := by sorry

alias «GlobalTheory».«TwoLines».«lact_one'» := P2M_GlobalTheory_TwoLines_lact_one__d9ee5c0b5a07
