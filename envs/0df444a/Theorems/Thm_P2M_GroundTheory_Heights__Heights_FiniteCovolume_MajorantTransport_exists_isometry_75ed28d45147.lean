-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_isometry_75ed28d45147
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_isometry_75ed28d45147
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:36.633356+00:00
-- url     : https://prove2.me/theorems/2a1b0623-0f0d-5174-9338-0b3f173f2e35
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists isometry 75ed28d45147: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists isometry 75ed28d45147
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists isometry 75ed28d45147 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport exists isometry 75ed28d45147 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L79-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L79-L113

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_isometry_75ed28d45147 {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v) :
    ∃ (d : ℕ) (S : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d)),
      ∀ y, ‖S y‖ = M.len y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«exists_isometry» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_isometry_75ed28d45147
