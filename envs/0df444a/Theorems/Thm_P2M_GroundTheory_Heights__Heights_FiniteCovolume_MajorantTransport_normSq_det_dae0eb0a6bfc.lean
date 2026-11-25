-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_normSq_det_dae0eb0a6bfc
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_normSq_det_dae0eb0a6bfc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:52.290734+00:00
-- url     : https://prove2.me/theorems/790336a4-b1b5-430e-b4be-64bf4c9e2dd1
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm Sq det dae0eb0a6bfc: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm Sq det dae0eb0a6bfc
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm Sq det dae0eb0a6bfc construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Transport norm Sq det dae0eb0a6bfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantTransport.lean#L40-L57

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
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_normSq_det_dae0eb0a6bfc (h : HermitianForm F E W) (v : Basis ι E W) (g : archUnitary h v)
    (w : InfinitePlace E) : Complex.normSq ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantTransport».«normSq_det» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_normSq_det_dae0eb0a6bfc
