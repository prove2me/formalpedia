-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c
-- name    : P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:36.036491+00:00
-- url     : https://prove2.me/theorems/db8437b6-e9dc-40a3-839c-5bffc5ce84de
-- title:
--   P2 M Ground Theory Heights  Heights local Lattice is Local Lattice dcaf16a6988c: P2 M Ground Theory Heights  Heights local Lattice is Local Lattice dcaf16a6988c
-- statement:
--   The P2 M Ground Theory Heights  Heights local Lattice is Local Lattice dcaf16a6988c construction uses the P2 M Ground Theory Heights  Heights local Lattice is Local Lattice dcaf16a6988c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L137-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L137-L167

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))

theorem P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c (L : FullLattice K V) :
    IsLocalLattice v (localLattice v L.carrier) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localLattice_isLocalLattice» := P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c
