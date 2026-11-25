-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjChowNonzero_eq_zero_of_isFiniteProjection_8c93cbd97ac1
-- name    : P2M_GroundTheory_Heights__Heights_ProjChowNonzero_eq_zero_of_isFiniteProjection_8c93cbd97ac1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:36.308592+00:00
-- url     : https://prove2.me/theorems/1571d985-b1dc-4e94-b957-271530471981
-- title:
--   P2 M Ground Theory Heights  Heights Proj Chow Nonzero eq zero of is Finite Projection 8c93cbd97ac1: P2 M Ground Theory Heights  Heights Proj Chow Nonzero eq zero of is Finite Projection 8c93cbd97ac1
-- statement:
--   The P2 M Ground Theory Heights  Heights Proj Chow Nonzero eq zero of is Finite Projection 8c93cbd97ac1 construction uses the P2 M Ground Theory Heights  Heights Proj Chow Nonzero eq zero of is Finite Projection 8c93cbd97ac1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L32-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjChowNonzero.lean#L32-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjChowNonzero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjChowNonzero
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
open GroundTheory.Heights₂.Heights.ProjChowNonzero

theorem P2M_GroundTheory_Heights__Heights_ProjChowNonzero_eq_zero_of_isFiniteProjection_8c93cbd97ac1 {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] {n d : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} (hW : IsHomogIdeal W)
    (hA : ComplexSets.IsFiniteProjection W A) {x : Fin n → Ω} (hx : ∀ q ∈ W, aeval x q = 0)
    (hAx : ∀ i, aeval x (ComplexSets.linPoly A i) = 0) : x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjChowNonzero».«eq_zero_of_isFiniteProjection» := P2M_GroundTheory_Heights__Heights_ProjChowNonzero_eq_zero_of_isFiniteProjection_8c93cbd97ac1
