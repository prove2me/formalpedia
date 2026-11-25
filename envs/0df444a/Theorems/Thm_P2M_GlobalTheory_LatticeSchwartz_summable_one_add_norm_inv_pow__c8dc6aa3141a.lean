-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LatticeSchwartz_summable_one_add_norm_inv_pow__c8dc6aa3141a
-- name    : P2M_GlobalTheory_LatticeSchwartz_summable_one_add_norm_inv_pow__c8dc6aa3141a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:12.212966+00:00
-- url     : https://prove2.me/theorems/25544cd1-2bcf-4a47-8638-cb17fcdf6ae2
-- title:
--   P2 M Global Theory Lattice Schwartz summable one add norm inv pow  c8dc6aa3141a: P2 M Global Theory Lattice Schwartz summable one add norm inv pow  c8dc6aa3141a
-- statement:
--   The P2 M Global Theory Lattice Schwartz summable one add norm inv pow  c8dc6aa3141a construction uses the P2 M Global Theory Lattice Schwartz summable one add norm inv pow  c8dc6aa3141a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeShiftedCutoffSummable.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeShiftedCutoffSummable.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeShiftedCutoffSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeSchwartz

theorem P2M_GlobalTheory_LatticeSchwartz_summable_one_add_norm_inv_pow__c8dc6aa3141a {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ}
    (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by sorry

alias «GlobalTheory».«LatticeSchwartz».«summable_one_add_norm_inv_pow'» := P2M_GlobalTheory_LatticeSchwartz_summable_one_add_norm_inv_pow__c8dc6aa3141a
