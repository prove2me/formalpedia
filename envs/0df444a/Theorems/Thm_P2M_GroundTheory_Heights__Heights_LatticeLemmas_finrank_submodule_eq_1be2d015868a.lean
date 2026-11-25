-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_submodule_eq_1be2d015868a
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_submodule_eq_1be2d015868a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:25.776909+00:00
-- url     : https://prove2.me/theorems/5ebfb22b-966a-5b48-9595-ed93121da751
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas finrank submodule eq 1be2d015868a: P2 M Ground Theory Heights  Heights Lattice Lemmas finrank submodule eq 1be2d015868a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas finrank submodule eq 1be2d015868a construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas finrank submodule eq 1be2d015868a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L102-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L102-L115

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_submodule_eq_1be2d015868a {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (F : Submodule R M) (hF : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ F) :
    Module.finrank R F = Module.finrank R M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«finrank_submodule_eq» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_submodule_eq_1be2d015868a
