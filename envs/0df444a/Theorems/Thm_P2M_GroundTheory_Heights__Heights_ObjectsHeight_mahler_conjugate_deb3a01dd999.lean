-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_conjugate_deb3a01dd999
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_conjugate_deb3a01dd999
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:23.166255+00:00
-- url     : https://prove2.me/theorems/4ed1f8dc-78b0-47ad-b5a5-73cb58d4d9ef
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height mahler conjugate deb3a01dd999: P2 M Ground Theory Heights  Heights Objects Height mahler conjugate deb3a01dd999
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height mahler conjugate deb3a01dd999 construction uses the P2 M Ground Theory Heights  Heights Objects Height mahler conjugate deb3a01dd999 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L423-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L423-L463

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_conjugate_deb3a01dd999 {K : Type*} [Field K] (h h' : HermNorm n)
    (hc : ∀ u, h'.norm (star u) = h.norm u) (σ : K →+* ℂ) (f : MvPolynomial (Fin k × Fin n) K) :
    mahler h' k (f.map (ComplexEmbedding.conjugate σ)) = mahler h k (f.map σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«mahler_conjugate» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_mahler_conjugate_deb3a01dd999
