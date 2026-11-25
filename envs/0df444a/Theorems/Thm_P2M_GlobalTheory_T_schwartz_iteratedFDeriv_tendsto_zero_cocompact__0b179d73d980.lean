-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_schwartz_iteratedFDeriv_tendsto_zero_cocompact__0b179d73d980
-- name    : P2M_GlobalTheory_T_schwartz_iteratedFDeriv_tendsto_zero_cocompact__0b179d73d980
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:57.326728+00:00
-- url     : https://prove2.me/theorems/c5a9374c-7833-498d-9e07-c9edbad47422
-- title:
--   P2 M Global Theory T schwartz iterated FDeriv tendsto zero cocompact  0b179d73d980: P2 M Global Theory T schwartz iterated FDeriv tendsto zero cocompact  0b179d73d980
-- statement:
--   The P2 M Global Theory T schwartz iterated FDeriv tendsto zero cocompact  0b179d73d980 construction uses the P2 M Global Theory T schwartz iterated FDeriv tendsto zero cocompact  0b179d73d980 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIteratedFDerivTendstoZeroCocompactStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIteratedFDerivTendstoZeroCocompactStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIteratedFDerivTendstoZeroCocompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_schwartz_iteratedFDeriv_tendsto_zero_cocompact__0b179d73d980 : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ), Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by sorry

alias «GlobalTheory».«T».«schwartz_iteratedFDeriv_tendsto_zero_cocompact'» := P2M_GlobalTheory_T_schwartz_iteratedFDeriv_tendsto_zero_cocompact__0b179d73d980
