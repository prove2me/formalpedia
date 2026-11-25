-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_isPrime_9038c2331720
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_isPrime_9038c2331720
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:21.51949+00:00
-- url     : https://prove2.me/theorems/b6e45493-1a49-5a8c-b768-78d2de8c637b
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart Q is Prime 9038c2331720: P2 M Ground Theory Heights  Heights Vertical Spec Chart Q is Prime 9038c2331720
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart Q is Prime 9038c2331720 construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart Q is Prime 9038c2331720 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L127-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_isPrime_9038c2331720 [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W) : (Q e I j W).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«Q_isPrime» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_Q_isPrime_9038c2331720
