-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archLattice_84196e4f1569
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archLattice_84196e4f1569
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:12.797133+00:00
-- url     : https://prove2.me/theorems/9be207d0-6ed6-40cb-9c64-e3849adecf75
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem arch Lattice 84196e4f1569: P2 M Ground Theory Heights  Heights Finite Covolume mem arch Lattice 84196e4f1569
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem arch Lattice 84196e4f1569 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem arch Lattice 84196e4f1569 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StArchCovolumeBound.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StArchCovolumeBound.lean#L26-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [IsTotallyComplex E] [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archLattice_84196e4f1569 {v : Basis ι E W} {La : AddSubgroup W} {y : InfinitePlace E → ι → ℂ} :
    y ∈ archLattice v La ↔ ∃ x ∈ La, vecAt v x = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_archLattice» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archLattice_84196e4f1569
