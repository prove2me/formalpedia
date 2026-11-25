-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dbl_good_11420f17daf7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dbl_good_11420f17daf7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:32.205508+00:00
-- url     : https://prove2.me/theorems/b5188cb1-6b0a-4dae-be77-98fe4b6ed429
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Double dbl good 11420f17daf7: P2 M Ground Theory Heights  Heights Kleiman Cech Double dbl good 11420f17daf7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Double dbl good 11420f17daf7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Double dbl good 11420f17daf7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L175-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDouble.lean#L175-L243

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble
open Cech
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {N r : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (r + 1) → Ω}
variable (M : Chart x → Chart y → Submodule S E)
variable {M}
variable (Ax : Chart x → Submodule S E) (Bx : Chart y → Submodule S E)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dbl_good_11420f17daf7 (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    (dbl Ax Bx hM₁ hM₂ hA hB).Good := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDouble».«dbl_good» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_dbl_good_11420f17daf7
