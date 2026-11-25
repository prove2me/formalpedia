-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_comm_f10b979213d4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_comm_f10b979213d4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:44.129039+00:00
-- url     : https://prove2.me/theorems/1fc69528-ece2-4ad1-a825-30214ced1626
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Form comm f10b979213d4: P2 M Ground Theory Heights  Heights Finite Covolume heis Form comm f10b979213d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Form comm f10b979213d4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Form comm f10b979213d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L41-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulus
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_comm_f10b979213d4 (hp : IsHyperbolicPair h x₀ w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = heisForm h v x₀ w₀ z y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisForm_comm» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_comm_f10b979213d4
