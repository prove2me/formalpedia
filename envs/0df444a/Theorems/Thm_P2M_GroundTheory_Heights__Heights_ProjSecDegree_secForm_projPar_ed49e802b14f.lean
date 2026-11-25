-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_secForm_projPar_ed49e802b14f
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDegree_secForm_projPar_ed49e802b14f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:42.623016+00:00
-- url     : https://prove2.me/theorems/5b45c6d2-6e05-53db-8e33-c22f36367fc3
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Degree sec Form proj Par ed49e802b14f: P2 M Ground Theory Heights  Heights Proj Sec Degree sec Form proj Par ed49e802b14f
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Degree sec Form proj Par ed49e802b14f construction uses the P2 M Ground Theory Heights  Heights Proj Sec Degree sec Form proj Par ed49e802b14f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L37-L45

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

theorem P2M_GroundTheory_Heights__Heights_ProjSecDegree_secForm_projPar_ed49e802b14f (i : Fin e) :
    Vertical.secForm (projPar A) i =
      C (projVar e i.succ) * (ComplexSets.linPoly A 0).map (algebraMap ℂ 𝕂) -
        C (projVar e 0) * (ComplexSets.linPoly A i.succ).map (algebraMap ℂ 𝕂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDegree».«secForm_projPar» := P2M_GroundTheory_Heights__Heights_ProjSecDegree_secForm_projPar_ed49e802b14f
