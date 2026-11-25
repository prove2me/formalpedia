-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ImaginaryLatticeCocompact_proof_764604f0b749
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ImaginaryLatticeCocompact_proof_764604f0b749
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:26:28.948121+00:00
-- url     : https://prove2.me/theorems/16d70330-f21c-59bf-8348-6a84173a7c1a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Imaginary Lattice Cocompact proof 764604f0b749: P2 M Ground Theory Heights  Heights Finite Covolume Imaginary Lattice Cocompact proof 764604f0b749
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Imaginary Lattice Cocompact proof 764604f0b749 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Imaginary Lattice Cocompact proof 764604f0b749 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L53-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L53-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PImaginaryLatticeCocompact
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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ImaginaryLatticeCocompact_proof_764604f0b749 : ImaginaryLatticeCocompact.Statement F E := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ImaginaryLatticeCocompact».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ImaginaryLatticeCocompact_proof_764604f0b749
