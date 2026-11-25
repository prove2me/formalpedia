-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_proof_286c88a5bb3c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_proof_286c88a5bb3c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:29.38889+00:00
-- url     : https://prove2.me/theorems/dcf818b6-050d-5b37-b6ca-5111259381c1
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact proof 286c88a5bb3c: P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact proof 286c88a5bb3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact proof 286c88a5bb3c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact proof 286c88a5bb3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L99-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L99-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
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
open scoped ComplexOrder
noncomputable section
open BoundedInverseCompact
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_proof_286c88a5bb3c (h : HermitianForm F E W) (v : Basis ι E W) :
    BoundedInverseCompact.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«BoundedInverseCompact».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_proof_286c88a5bb3c
