-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eval_scaleP_593c7fecc608
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_eval_scaleP_593c7fecc608
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:32.131661+00:00
-- url     : https://prove2.me/theorems/b5909277-2a78-4e4d-becd-3a4bbe3c5efb
-- title:
--   P2 M Ground Theory Heights  Heights Log Int eval scale P 593c7fecc608: P2 M Ground Theory Heights  Heights Log Int eval scale P 593c7fecc608
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int eval scale P 593c7fecc608 construction uses the P2 M Ground Theory Heights  Heights Log Int eval scale P 593c7fecc608 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L36-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_eval_scaleP_593c7fecc608 (p : ι → Prop) [DecidablePred p] (a : ℂ) (u : ι → ℂ) (g : MvPolynomial ι ℂ)
    (D : ℕ) (hD : ∀ m ∈ g.support, Finsupp.weight (indW p) m ≤ D) :
    eval (scaleP p a u) g =
      ∑ d ∈ Finset.range (D + 1), eval u (weightedHomogeneousComponent (indW p) d g) * a ^ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«eval_scaleP» := P2M_GroundTheory_Heights__Heights_LogInt_eval_scaleP_593c7fecc608
