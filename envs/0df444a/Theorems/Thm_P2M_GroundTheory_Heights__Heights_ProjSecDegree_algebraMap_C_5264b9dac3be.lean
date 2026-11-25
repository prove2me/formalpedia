-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_algebraMap_C_5264b9dac3be
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDegree_algebraMap_C_5264b9dac3be
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:45.811307+00:00
-- url     : https://prove2.me/theorems/4f80c463-ab7c-4503-8052-d7978d028ff9
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Degree algebra Map C 5264b9dac3be: P2 M Ground Theory Heights  Heights Proj Sec Degree algebra Map C 5264b9dac3be
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Degree algebra Map C 5264b9dac3be construction uses the P2 M Ground Theory Heights  Heights Proj Sec Degree algebra Map C 5264b9dac3be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDegree
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjSecDegree
variable {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
local notation "𝕂" => FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
local notation "ℝt" => MvPolynomial (Fin (e + 1)) ℂ

theorem P2M_GroundTheory_Heights__Heights_ProjSecDegree_algebraMap_C_5264b9dac3be (c : ℂ) : algebraMap ℝt 𝕂 (C c) = algebraMap ℂ 𝕂 c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDegree».«algebraMap_C» := P2M_GroundTheory_Heights__Heights_ProjSecDegree_algebraMap_C_5264b9dac3be
