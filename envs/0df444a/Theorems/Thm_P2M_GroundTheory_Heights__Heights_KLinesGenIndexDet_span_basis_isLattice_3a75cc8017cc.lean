-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexDet_span_basis_isLattice_3a75cc8017cc
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGenIndexDet_span_basis_isLattice_3a75cc8017cc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:48.212407+00:00
-- url     : https://prove2.me/theorems/548760e2-cee0-4fdc-b6a8-6873bf0319af
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gen Index Det span basis is Lattice 3a75cc8017cc: P2 M Ground Theory Heights  Heights KLines Gen Index Det span basis is Lattice 3a75cc8017cc
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gen Index Det span basis is Lattice 3a75cc8017cc construction uses the P2 M Ground Theory Heights  Heights KLines Gen Index Det span basis is Lattice 3a75cc8017cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexDet.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexDet.lean#L9-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.KLinesGenIndexDet

theorem P2M_GroundTheory_Heights__Heights_KLinesGenIndexDet_span_basis_isLattice_3a75cc8017cc {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGenIndexDet».«span_basis_isLattice» := P2M_GroundTheory_Heights__Heights_KLinesGenIndexDet_span_basis_isLattice_3a75cc8017cc
