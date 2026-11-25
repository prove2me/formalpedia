-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_heisConjLin_bafb153a3731
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_heisConjLin_bafb153a3731
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:11.056339+00:00
-- url     : https://prove2.me/theorems/63f063f3-076e-5300-8318-660be6cdcf33
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Form heis Conj Lin bafb153a3731: P2 M Ground Theory Heights  Heights Finite Covolume heis Form heis Conj Lin bafb153a3731
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Form heis Conj Lin bafb153a3731 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Form heis Conj Lin bafb153a3731 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L102-L107

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_heisConjLin_bafb153a3731 (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ (heisConjLin g hg y) (heisConjLin g hg z) = heisForm h v x₀ w₀ y z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisForm_heisConjLin» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_heisConjLin_bafb153a3731
