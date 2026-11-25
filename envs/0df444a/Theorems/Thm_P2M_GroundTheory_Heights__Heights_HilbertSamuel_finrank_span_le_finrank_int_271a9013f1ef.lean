-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_finrank_span_le_finrank_int_271a9013f1ef
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_finrank_span_le_finrank_int_271a9013f1ef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:00.698878+00:00
-- url     : https://prove2.me/theorems/153addd2-7436-4152-abd9-c8c95757524b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel finrank span le finrank int 271a9013f1ef: P2 M Ground Theory Heights  Heights Hilbert Samuel finrank span le finrank int 271a9013f1ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel finrank span le finrank int 271a9013f1ef construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel finrank span le finrank int 271a9013f1ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPacking.lean#L54-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPacking.lean#L54-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPacking
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Metric Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_finrank_span_le_finrank_int_271a9013f1ef {V : Type*} [AddCommGroup V] [Module ℝ V]
    (La : Submodule ℤ V) [Module.Finite ℤ La] :
    (La : Set V) ⊆ Submodule.span ℝ (La : Set V) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (La : Set V)) ∧
      finrank ℝ (Submodule.span ℝ (La : Set V)) ≤ finrank ℤ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«finrank_span_le_finrank_int» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_finrank_span_le_finrank_int_271a9013f1ef
