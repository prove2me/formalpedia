-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_locQuotSemilinear_injective_33b0e5b56582
-- name    : P2M_GroundTheory_Heights__Heights_locQuotSemilinear_injective_33b0e5b56582
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:26.322477+00:00
-- url     : https://prove2.me/theorems/98cb367c-61f7-42d7-af1b-420970b3aa8e
-- title:
--   P2 M Ground Theory Heights  Heights loc Quot Semilinear injective 33b0e5b56582: P2 M Ground Theory Heights  Heights loc Quot Semilinear injective 33b0e5b56582
-- statement:
--   The P2 M Ground Theory Heights  Heights loc Quot Semilinear injective 33b0e5b56582 construction uses the P2 M Ground Theory Heights  Heights loc Quot Semilinear injective 33b0e5b56582 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L124-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L124-L138

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

theorem P2M_GroundTheory_Heights__Heights_locQuotSemilinear_injective_33b0e5b56582 : Function.Injective (locQuotSemilinear σ J V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«locQuotSemilinear_injective» := P2M_GroundTheory_Heights__Heights_locQuotSemilinear_injective_33b0e5b56582
