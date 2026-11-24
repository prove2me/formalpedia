-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_map_mk_isPrime_117a21e5f9cd
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_map_mk_isPrime_117a21e5f9cd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:40.150807+00:00
-- url     : https://prove2.me/theorems/69a3c5a0-9b24-467d-a669-222825574ae4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Spec Chart map mk is Prime 117a21e5f9cd: P2 M Ground Theory Heights  Heights Vertical Spec Chart map mk is Prime 117a21e5f9cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Spec Chart map mk is Prime 117a21e5f9cd construction uses the P2 M Ground Theory Heights  Heights Vertical Spec Chart map mk is Prime 117a21e5f9cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartIso.lean#L100-L102

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_map_mk_isPrime_117a21e5f9cd [W.IsPrime] (hPW : integralModel I ≤ W) :
    (W.map (Ideal.Quotient.mk (integralModel I))).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SpecChart».«map_mk_isPrime» := P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_map_mk_isPrime_117a21e5f9cd
