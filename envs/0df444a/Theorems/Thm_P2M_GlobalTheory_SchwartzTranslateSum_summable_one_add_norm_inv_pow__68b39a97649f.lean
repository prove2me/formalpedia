-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SchwartzTranslateSum_summable_one_add_norm_inv_pow__68b39a97649f
-- name    : P2M_GlobalTheory_SchwartzTranslateSum_summable_one_add_norm_inv_pow__68b39a97649f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:49.835212+00:00
-- url     : https://prove2.me/theorems/bfe5e99b-df12-4b01-aa96-3262dbbf144e
-- title:
--   P2 M Global Theory Schwartz Translate Sum summable one add norm inv pow  68b39a97649f: P2 M Global Theory Schwartz Translate Sum summable one add norm inv pow  68b39a97649f
-- statement:
--   The P2 M Global Theory Schwartz Translate Sum summable one add norm inv pow  68b39a97649f construction uses the P2 M Global Theory Schwartz Translate Sum summable one add norm inv pow  68b39a97649f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeTranslatesCutoffSummable.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeTranslatesCutoffSummable.lean#L9-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeTranslatesCutoffSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap
noncomputable section
open GlobalTheory GlobalTheory.SchwartzTranslateSum

theorem P2M_GlobalTheory_SchwartzTranslateSum_summable_one_add_norm_inv_pow__68b39a97649f {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] {N : ℕ}
    (hN : Module.finrank ℤ Λ < N) : Summable fun z : Λ => ((1 + ‖z‖)⁻¹) ^ N := by sorry

alias «GlobalTheory».«SchwartzTranslateSum».«summable_one_add_norm_inv_pow'» := P2M_GlobalTheory_SchwartzTranslateSum_summable_one_add_norm_inv_pow__68b39a97649f
