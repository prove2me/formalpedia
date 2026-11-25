-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_conjTranspose_mul_self_056b80eec094
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_conjTranspose_mul_self_056b80eec094
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:17.458029+00:00
-- url     : https://prove2.me/theorems/4b7ef294-b49c-4bd6-9637-118a0cfef133
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists conj Transpose mul self 056b80eec094: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists conj T
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists conj Transpose mul self 056b80eec094 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists conj Transpose mul self 056b80eec094 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L17-L21

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
open GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_conjTranspose_mul_self_056b80eec094 {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ X : Matrix ι ι ℂ, Xᴴ * X = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«exists_conjTranspose_mul_self» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_conjTranspose_mul_self_056b80eec094
