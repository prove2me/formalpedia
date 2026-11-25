-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:04:09.977462+00:00
-- url     : https://prove2.me/theorems/2a074dee-3764-599b-a293-55463a5f9199
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Form apply 314ec8cdf0d6: P2 M Ground Theory Heights  Heights Finite Covolume heis Form apply 314ec8cdf0d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Form apply 314ec8cdf0d6 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Form apply 314ec8cdf0d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L37-L39

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
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6 (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisForm_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisForm_apply_314ec8cdf0d6
