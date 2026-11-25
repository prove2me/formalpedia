-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumAdditive_proof_a78390f278f3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumAdditive_proof_a78390f278f3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:44:14.844491+00:00
-- url     : https://prove2.me/theorems/4ecacc3c-b820-454d-a636-e8cd8915866f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Additive proof a78390f278f3: P2 M Ground Theory Heights  Heights Kleiman Inter Num Additive proof a78390f278f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Additive proof a78390f278f3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Additive proof a78390f278f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L123-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumAdditive.lean#L123-L175

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterSumTopVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumAdditive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
attribute [local instance] twistMonoid

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumAdditive_proof_a78390f278f3 (hE : InterNumEventual.Statement.{u, w})
    (hZ : InterSumTopVanish.Statement.{u, w}) : InterNumAdditive.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumAdditive».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumAdditive_proof_a78390f278f3
