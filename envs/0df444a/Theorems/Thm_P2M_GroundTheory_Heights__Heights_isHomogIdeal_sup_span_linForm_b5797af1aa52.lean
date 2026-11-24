-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52
-- name    : P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:17.874044+00:00
-- url     : https://prove2.me/theorems/4aa433a4-539d-4689-a259-e9db8de5b5d3
-- title:
--   P2 M Ground Theory Heights  Heights is Homog Ideal sup span lin Form b5797af1aa52: P2 M Ground Theory Heights  Heights is Homog Ideal sup span lin Form b5797af1aa52
-- statement:
--   The P2 M Ground Theory Heights  Heights is Homog Ideal sup span lin Form b5797af1aa52 construction uses the P2 M Ground Theory Heights  Heights is Homog Ideal sup span lin Form b5797af1aa52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L93-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type*} [CommRing R] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52 {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I)
    (u : Fin n → R) : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isHomogIdeal_sup_span_linForm» := P2M_GroundTheory_Heights__Heights_isHomogIdeal_sup_span_linForm_b5797af1aa52
