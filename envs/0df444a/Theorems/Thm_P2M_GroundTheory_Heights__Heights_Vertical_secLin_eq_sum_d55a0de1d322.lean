-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_sum_d55a0de1d322
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_sum_d55a0de1d322
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:40.279422+00:00
-- url     : https://prove2.me/theorems/4279d002-14f7-41a4-aa0d-775b0db70dc8
-- title:
--   P2 M Ground Theory Heights  Heights Vertical sec Lin eq sum d55a0de1d322: P2 M Ground Theory Heights  Heights Vertical sec Lin eq sum d55a0de1d322
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical sec Lin eq sum d55a0de1d322 construction uses the P2 M Ground Theory Heights  Heights Vertical sec Lin eq sum d55a0de1d322 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PNormIdentity.lean#L64-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormIdentity
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
variable {K : Type*} [Field K] [NumberField K] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_sum_d55a0de1d322 {R : Type*} [CommRing R] {Q : Ideal (MvPolynomial (Fin n) R)} {y : Par e n → R}
    (w : Fin n → R) : secLin Q y w = ∑ j, algebraMap R (SecAlg Q y) (w j) * secCoord Q y j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«secLin_eq_sum» := P2M_GroundTheory_Heights__Heights_Vertical_secLin_eq_sum_d55a0de1d322
