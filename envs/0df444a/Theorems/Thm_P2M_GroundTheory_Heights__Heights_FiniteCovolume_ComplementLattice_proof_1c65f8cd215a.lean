-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementLattice_proof_1c65f8cd215a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementLattice_proof_1c65f8cd215a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:20:04.565665+00:00
-- url     : https://prove2.me/theorems/b59bdd35-45ab-5e40-80e2-436d539d1ffb
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Lattice proof 1c65f8cd215a: P2 M Ground Theory Heights  Heights Finite Covolume Complement Lattice proof 1c65f8cd215a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Lattice proof 1c65f8cd215a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Lattice proof 1c65f8cd215a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L47-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementLattice.lean#L47-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementLattice_proof_1c65f8cd215a (h : HermitianForm F E W) [FiniteDimensional E W] :
    ComplementLattice.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementLattice».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementLattice_proof_1c65f8cd215a
