-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_mulVec_8a450dd7dca1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_mulVec_8a450dd7dca1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:26.51124+00:00
-- url     : https://prove2.me/theorems/a512c1e2-c9e3-4bcd-b49d-f6bda476cec8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserving mul Vec 8a450dd7dca1: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preservin
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserving mul Vec 8a450dd7dca1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserving mul Vec 8a450dd7dca1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L23-L36

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_mulVec_8a450dd7dca1 {A : Matrix ι ι ℂ} (hA : Complex.normSq A.det = 1) :
    MeasurePreserving (fun z : ι → ℂ => A *ᵥ z) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«measurePreserving_mulVec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_mulVec_8a450dd7dca1
