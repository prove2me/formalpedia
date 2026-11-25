-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_locQuotSemilinear_surjective_746a40a56a06
-- name    : P2M_GroundTheory_Heights__Heights_locQuotSemilinear_surjective_746a40a56a06
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:48.961741+00:00
-- url     : https://prove2.me/theorems/94d3ee5e-d04a-488c-b007-f903ff6f6f6c
-- title:
--   P2 M Ground Theory Heights  Heights loc Quot Semilinear surjective 746a40a56a06: P2 M Ground Theory Heights  Heights loc Quot Semilinear surjective 746a40a56a06
-- statement:
--   The P2 M Ground Theory Heights  Heights loc Quot Semilinear surjective 746a40a56a06 construction uses the P2 M Ground Theory Heights  Heights loc Quot Semilinear surjective 746a40a56a06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L140-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L140-L149

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

theorem P2M_GroundTheory_Heights__Heights_locQuotSemilinear_surjective_746a40a56a06 : Function.Surjective (locQuotSemilinear σ J V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«locQuotSemilinear_surjective» := P2M_GroundTheory_Heights__Heights_locQuotSemilinear_surjective_746a40a56a06
