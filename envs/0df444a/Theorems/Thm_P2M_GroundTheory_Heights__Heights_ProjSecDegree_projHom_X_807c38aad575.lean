-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_X_807c38aad575
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_X_807c38aad575
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:32.468751+00:00
-- url     : https://prove2.me/theorems/f5fe130c-56c5-41a4-b6e5-67de0c9c3cc9
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom X 807c38aad575: P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom X 807c38aad575
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom X 807c38aad575 construction uses the P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom X 807c38aad575 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L51-L53

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

theorem P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_X_807c38aad575 (i : Fin (e + 1)) :
    ComplexSets.projHom J A (X i) = Ideal.Quotient.mk J (ComplexSets.linPoly A i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDegree».«projHom_X» := P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_X_807c38aad575
