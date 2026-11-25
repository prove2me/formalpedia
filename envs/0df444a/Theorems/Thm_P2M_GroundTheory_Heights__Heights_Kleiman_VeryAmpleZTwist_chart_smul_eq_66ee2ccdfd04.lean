-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_chart_smul_eq_66ee2ccdfd04
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_chart_smul_eq_66ee2ccdfd04
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:38.201146+00:00
-- url     : https://prove2.me/theorems/122be7c2-7a71-48ec-86ed-185683e57677
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist chart smul eq 66ee2ccdfd04: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist chart smul eq 66ee2ccdfd04
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist chart smul eq 66ee2ccdfd04 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist chart smul eq 66ee2ccdfd04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L21-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_chart_smul_eq_66ee2ccdfd04 {I : Chart x} (c : chartRing S x I) (z : E) : c • z = (c : Ω) • z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZTwist».«chart_smul_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_chart_smul_eq_66ee2ccdfd04
