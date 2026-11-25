-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sphereMean_eq_8b9830c2c5f6
-- name    : P2M_GroundTheory_Heights__Heights_sphereMean_eq_8b9830c2c5f6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:29.963076+00:00
-- url     : https://prove2.me/theorems/80bd230d-3664-4611-a3ba-3edbddb3b70f
-- title:
--   P2 M Ground Theory Heights  Heights sphere Mean eq 8b9830c2c5f6: P2 M Ground Theory Heights  Heights sphere Mean eq 8b9830c2c5f6
-- statement:
--   The P2 M Ground Theory Heights  Heights sphere Mean eq 8b9830c2c5f6 construction uses the P2 M Ground Theory Heights  Heights sphere Mean eq 8b9830c2c5f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/IsProbabilityMeasureSphereLaw.lean#L81-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
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
open MvPolynomial NumberField MeasureTheory ProbabilityTheory TensorProduct ComplexAt
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_sphereMean_eq_8b9830c2c5f6 (h : HermNorm n) (k : ℕ) (g : (Fin k × Fin n → ℂ) → ℝ) :
    sphereMean h k g = ⨍ u in sphereBall h k, g (sphereNormalize h k u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sphereMean_eq» := P2M_GroundTheory_Heights__Heights_sphereMean_eq_8b9830c2c5f6
