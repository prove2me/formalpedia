-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_invApply_1be71f7a5040
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_invApply_1be71f7a5040
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:39:45.758892+00:00
-- url     : https://prove2.me/theorems/1f4c8b96-3e6b-4bdf-a386-541e3c1e4ced
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserving inv Apply 1be71f7a5040: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserv
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserving inv Apply 1be71f7a5040 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport measure Preserving inv Apply 1be71f7a5040 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L127-L130

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
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_invApply_1be71f7a5040 {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) : MeasurePreserving (invApply g) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«measurePreserving_invApply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_measurePreserving_invApply_1be71f7a5040
