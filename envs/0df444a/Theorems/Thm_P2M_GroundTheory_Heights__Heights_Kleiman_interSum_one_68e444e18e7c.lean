-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interSum_one_68e444e18e7c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interSum_one_68e444e18e7c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:40.519457+00:00
-- url     : https://prove2.me/theorems/0ef5fac8-0f13-5fa3-96ea-e894c19e7d43
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Sum one 68e444e18e7c: P2 M Ground Theory Heights  Heights Kleiman inter Sum one 68e444e18e7c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Sum one 68e444e18e7c construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Sum one 68e444e18e7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L18-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interSum_one_68e444e18e7c (pp : Ideal (Poly S N)) (L : SubSystem S x Ω) (c : ℕ) :
    interSum pp ![L] c = restrLen pp (L.twist (twistSys S x (c : ℤ))) -
      restrLen pp ((twistSys S x 0).twist (twistSys S x (c : ℤ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interSum_one» := P2M_GroundTheory_Heights__Heights_Kleiman_interSum_one_68e444e18e7c
