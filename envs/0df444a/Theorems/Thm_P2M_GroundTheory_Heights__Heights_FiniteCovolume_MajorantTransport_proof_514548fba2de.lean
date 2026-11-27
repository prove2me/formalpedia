-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_proof_514548fba2de
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_proof_514548fba2de
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:53.6407+00:00
-- url     : https://prove2.me/theorems/dc6ab230-a1cd-5e29-b05c-fd2452be0d64
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport proof 514548fba2de: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport proof 514548fba2de
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport proof 514548fba2de construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport proof 514548fba2de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L136-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L136-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantTransport
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
open scoped MatrixOrder ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_proof_514548fba2de (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantTransport.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_proof_514548fba2de
