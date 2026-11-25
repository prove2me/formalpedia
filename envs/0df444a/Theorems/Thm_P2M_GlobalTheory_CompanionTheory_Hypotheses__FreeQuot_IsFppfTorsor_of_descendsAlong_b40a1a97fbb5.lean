-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_of_descendsAlong_b40a1a97fbb5
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_of_descendsAlong_b40a1a97fbb5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:21.756798+00:00
-- url     : https://prove2.me/theorems/0f5422bb-76ee-4006-aab4-fa05a244e53a
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor of descends Along b40a1a97fbb5: P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor of descends Along b40a
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor of descends Along b40a1a97fbb5 construction uses the P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor of descends Along b40a1a97fbb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L105-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L105-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂
open FreeQuot
open GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
universe u
variable {S : Scheme.{u}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
set_option backward.isDefEq.respectTransparency.types false

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_of_descendsAlong_b40a1a97fbb5 (h : IsFppfTorsor G q) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (hG : P G.hom) : P q.left := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«FreeQuot».«IsFppfTorsor».«of_descendsAlong» := P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_of_descendsAlong_b40a1a97fbb5
