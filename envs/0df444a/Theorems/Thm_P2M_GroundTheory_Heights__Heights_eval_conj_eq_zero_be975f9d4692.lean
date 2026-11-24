-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_conj_eq_zero_be975f9d4692
-- name    : P2M_GroundTheory_Heights__Heights_eval_conj_eq_zero_be975f9d4692
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:47.375309+00:00
-- url     : https://prove2.me/theorems/490ae51d-b71e-4c27-8b00-69604f20aec2
-- title:
--   P2 M Ground Theory Heights  Heights eval conj eq zero be975f9d4692: P2 M Ground Theory Heights  Heights eval conj eq zero be975f9d4692
-- statement:
--   The P2 M Ground Theory Heights  Heights eval conj eq zero be975f9d4692 construction uses the P2 M Ground Theory Heights  Heights eval conj eq zero be975f9d4692 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L75-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_eval_conj_eq_zero_be975f9d4692 [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ →+* ℂ)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) :
    eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_conj_eq_zero» := P2M_GroundTheory_Heights__Heights_eval_conj_eq_zero_be975f9d4692
