-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_continuousMultilinearMap_ext_hilbertBasis__17824b0f27f8
-- name    : P2M_GlobalTheory_T_continuousMultilinearMap_ext_hilbertBasis__17824b0f27f8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:04:52.418444+00:00
-- url     : https://prove2.me/theorems/e228b4b6-7d92-4159-8983-a7159d35d985
-- title:
--   P2 M Global Theory T continuous Multilinear Map ext hilbert Basis  17824b0f27f8: P2 M Global Theory T continuous Multilinear Map ext hilbert Basis  17824b0f27f8
-- statement:
--   The P2 M Global Theory T continuous Multilinear Map ext hilbert Basis  17824b0f27f8 construction uses the P2 M Global Theory T continuous Multilinear Map ext hilbert Basis  17824b0f27f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousMultilinearMapExtHilbertBasisStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousMultilinearMapExtHilbertBasisStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMultilinearMapExtHilbertBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMultilinearMapExtHilbertBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_continuousMultilinearMap_ext_hilbertBasis__17824b0f27f8 : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F), (∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) → f = g := by sorry

alias «GlobalTheory».«T».«continuousMultilinearMap_ext_hilbertBasis'» := P2M_GlobalTheory_T_continuousMultilinearMap_ext_hilbertBasis__17824b0f27f8
