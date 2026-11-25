-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_chartForm_projPar_2d49b4866f36
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDegree_chartForm_projPar_2d49b4866f36
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:05.99643+00:00
-- url     : https://prove2.me/theorems/96b3cdd3-22db-57a2-aec5-669dbfeabd63
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Degree chart Form proj Par 2d49b4866f36: P2 M Ground Theory Heights  Heights Proj Sec Degree chart Form proj Par 2d49b4866f36
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Degree chart Form proj Par 2d49b4866f36 construction uses the P2 M Ground Theory Heights  Heights Proj Sec Degree chart Form proj Par 2d49b4866f36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L29-L35

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

theorem P2M_GroundTheory_Heights__Heights_ProjSecDegree_chartForm_projPar_2d49b4866f36 :
    Vertical.chartForm (projPar A) =
      C (projVar e 0)⁻¹ * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDegree».«chartForm_projPar» := P2M_GroundTheory_Heights__Heights_ProjSecDegree_chartForm_projPar_2d49b4866f36
