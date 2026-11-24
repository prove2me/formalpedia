-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_pow_3db7e9c92ffa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_pow_3db7e9c92ffa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:48.408252+00:00
-- url     : https://prove2.me/theorems/7a11e1e4-90d5-407a-83d9-f9a6d2eee9b0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub pow 3db7e9c92ffa: P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub pow 3db7e9c92ffa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub pow 3db7e9c92ffa construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Cover sub pow 3db7e9c92ffa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleCover.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleCover.lean#L27-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleCover
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_pow_3db7e9c92ffa (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleCover».«sub_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_pow_3db7e9c92ffa
