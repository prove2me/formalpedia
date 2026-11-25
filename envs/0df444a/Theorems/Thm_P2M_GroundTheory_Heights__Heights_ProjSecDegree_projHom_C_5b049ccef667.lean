-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_C_5b049ccef667
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_C_5b049ccef667
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:44.222622+00:00
-- url     : https://prove2.me/theorems/ded37002-755a-44e8-b0cc-2eedcc1b5fc2
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom C 5b049ccef667: P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom C 5b049ccef667
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom C 5b049ccef667 construction uses the P2 M Ground Theory Heights  Heights Proj Sec Degree proj Hom C 5b049ccef667 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L47-L49

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

theorem P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_C_5b049ccef667 (c : ℂ) : ComplexSets.projHom J A (C c) = Ideal.Quotient.mk J (C c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDegree».«projHom_C» := P2M_GroundTheory_Heights__Heights_ProjSecDegree_projHom_C_5b049ccef667
