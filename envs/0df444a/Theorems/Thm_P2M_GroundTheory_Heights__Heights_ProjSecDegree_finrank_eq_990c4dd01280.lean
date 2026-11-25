-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjSecDegree_finrank_eq_990c4dd01280
-- name    : P2M_GroundTheory_Heights__Heights_ProjSecDegree_finrank_eq_990c4dd01280
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:47.424868+00:00
-- url     : https://prove2.me/theorems/6c11651d-6348-4149-9886-e80b07cd7429
-- title:
--   P2 M Ground Theory Heights  Heights Proj Sec Degree finrank eq 990c4dd01280: P2 M Ground Theory Heights  Heights Proj Sec Degree finrank eq 990c4dd01280
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Sec Degree finrank eq 990c4dd01280 construction uses the P2 M Ground Theory Heights  Heights Proj Sec Degree finrank eq 990c4dd01280 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L58-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean#L58-L154

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
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem P2M_GroundTheory_Heights__Heights_ProjSecDegree_finrank_eq_990c4dd01280 [Algebra ℝt (MvPolynomial (Fin n) ℂ ⧸ J)]
    (hφ : ∀ p, algebraMap ℝt (MvPolynomial (Fin n) ℂ ⧸ J) p = ComplexSets.projHom J A p) :
    Module.finrank 𝕂 (TensorProduct ℝt 𝕂 (MvPolynomial (Fin n) ℂ ⧸ J)) =
      Module.finrank 𝕂
        (Vertical.SecAlg (J.map (MvPolynomial.map (algebraMap ℂ 𝕂))) (projPar A)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjSecDegree».«finrank_eq» := P2M_GroundTheory_Heights__Heights_ProjSecDegree_finrank_eq_990c4dd01280
