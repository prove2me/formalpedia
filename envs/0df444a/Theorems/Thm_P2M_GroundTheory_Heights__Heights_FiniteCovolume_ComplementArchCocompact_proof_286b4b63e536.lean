-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_proof_286b4b63e536
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_proof_286b4b63e536
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:25:33.933905+00:00
-- url     : https://prove2.me/theorems/4a2cbd3b-ca73-5cc0-b1ed-fb2cf4dc2ce9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proof 286b4b63e536: P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proof 286b4b63e536
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proof 286b4b63e536 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Complement Arch Cocompact proof 286b4b63e536 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L70-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PComplementArchCocompact.lean#L70-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsZsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementArchCocompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordEmbedBasis_proof_0ebb0c03bf39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open ComplementArchCocompact

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_proof_286b4b63e536 (h : HermitianForm F E W) (v : Basis ι E W) :
    ComplementArchCocompact.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ComplementArchCocompact».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_proof_286b4b63e536
