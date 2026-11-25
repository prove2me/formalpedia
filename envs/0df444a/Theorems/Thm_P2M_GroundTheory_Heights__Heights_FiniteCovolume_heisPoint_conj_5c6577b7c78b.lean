-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_conj_5c6577b7c78b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_conj_5c6577b7c78b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:22.497863+00:00
-- url     : https://prove2.me/theorems/52080c10-1025-5275-9409-424d886093a8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Point conj 5c6577b7c78b: P2 M Ground Theory Heights  Heights Finite Covolume heis Point conj 5c6577b7c78b
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Point conj 5c6577b7c78b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Point conj 5c6577b7c78b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L163-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L163-L176

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusCoords
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_conj_5c6577b7c78b (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisConjLin g hg p.1, p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisPoint_conj» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_conj_5c6577b7c78b
