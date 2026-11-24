-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_locQuotSemilinear_apply_1c8e21b617b3
-- name    : P2M_GroundTheory_Heights__Heights_locQuotSemilinear_apply_1c8e21b617b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:51.499825+00:00
-- url     : https://prove2.me/theorems/339fa62d-87d1-4fc1-9af8-c7729e588f45
-- title:
--   P2 M Ground Theory Heights  Heights loc Quot Semilinear apply 1c8e21b617b3: P2 M Ground Theory Heights  Heights loc Quot Semilinear apply 1c8e21b617b3
-- statement:
--   The P2 M Ground Theory Heights  Heights loc Quot Semilinear apply 1c8e21b617b3 construction uses the P2 M Ground Theory Heights  Heights loc Quot Semilinear apply 1c8e21b617b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L121-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]

theorem P2M_GroundTheory_Heights__Heights_locQuotSemilinear_apply_1c8e21b617b3 (x : LocalizedModule V.primeCompl (A ⧸ J)) :
    locQuotSemilinear σ J V x = locQuotMap σ J V x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«locQuotSemilinear_apply» := P2M_GroundTheory_Heights__Heights_locQuotSemilinear_apply_1c8e21b617b3
