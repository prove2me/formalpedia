-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_VolumePreservingUncurry_volume_preserving_uncurry__ff0a4f2b7d3b
-- name    : P2M_UpperTheory_Reformulated_B_VolumePreservingUncurry_volume_preserving_uncurry__ff0a4f2b7d3b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:37.941167+00:00
-- url     : https://prove2.me/theorems/e4d9c32f-ea11-5ca0-84eb-9a45acfca22a
-- title:
--   P2 M Upper Theory Reformulated B Volume Preserving Uncurry volume preserving uncurry  ff0a4f2b7d3b: P2 M Upper Theory Reformulated B Volume Preserving Uncurry volume preserving uncurry  ff0a4f2b7d3b
-- statement:
--   The P2 M Upper Theory Reformulated B Volume Preserving Uncurry volume preserving uncurry  ff0a4f2b7d3b construction uses the P2 M Upper Theory Reformulated B Volume Preserving Uncurry volume preserving uncurry  ff0a4f2b7d3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/VolumePreservingUncurry.lean#L3-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/VolumePreservingUncurry.lean#L3-L34

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VolumePreservingUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_VolumePreservingUncurry_volume_preserving_uncurry__ff0a4f2b7d3b.{u_1, u_2} :
    ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype ι] [inst_1 : Fintype κ],
      @MeasureTheory.MeasurePreserving (ι → κ → Real) (Prod ι κ → Real)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace))
        (@Function.uncurry ι κ Real)
        (@MeasureTheory.MeasureSpace.volume (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace)) := by sorry

alias «UpperTheory».«Reformulated».«B».«VolumePreservingUncurry».«volume_preserving_uncurry».«» := P2M_UpperTheory_Reformulated_B_VolumePreservingUncurry_volume_preserving_uncurry__ff0a4f2b7d3b
