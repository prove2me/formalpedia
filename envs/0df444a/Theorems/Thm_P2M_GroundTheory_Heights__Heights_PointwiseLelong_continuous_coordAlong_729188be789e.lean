-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:03.055963+00:00
-- url     : https://prove2.me/theorems/90fec13a-7dbc-48cb-ac7c-4771a6e310e9
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong continuous coord Along 729188be789e: P2 M Ground Theory Heights  Heights Pointwise Lelong continuous coord Along 729188be789e
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong continuous coord Along 729188be789e construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong continuous coord Along 729188be789e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L163-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L163-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e (p : Fin N → ℂ) : Continuous (coordAlong p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«continuous_coordAlong» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
