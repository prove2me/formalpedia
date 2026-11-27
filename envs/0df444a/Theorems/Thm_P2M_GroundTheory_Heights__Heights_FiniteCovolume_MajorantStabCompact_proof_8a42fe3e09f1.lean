-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_proof_8a42fe3e09f1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_proof_8a42fe3e09f1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:26:30.116294+00:00
-- url     : https://prove2.me/theorems/fbe9467b-a3b7-4794-915d-b8927c61fbf3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact proof 8a42fe3e09f1: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact proof 8a42fe3e09f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact proof 8a42fe3e09f1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact proof 8a42fe3e09f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantStabCompact.lean#L33-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantStabCompact.lean#L33-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsMajorantStabCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantStabCompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_proof_286c88a5bb3c

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
open MajorantStabCompact
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_proof_8a42fe3e09f1 (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantStabCompact».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_proof_8a42fe3e09f1
