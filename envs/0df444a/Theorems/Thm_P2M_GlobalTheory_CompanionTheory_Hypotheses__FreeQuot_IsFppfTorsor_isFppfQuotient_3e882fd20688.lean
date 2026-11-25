-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFppfQuotient_3e882fd20688
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFppfQuotient_3e882fd20688
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:48.486988+00:00
-- url     : https://prove2.me/theorems/8c389203-97f0-479f-a743-5c96ff362670
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Fppf Quotient 3e882fd20688: P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Fppf Quotient 3e882f
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Fppf Quotient 3e882fd20688 construction uses the P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Fppf Quotient 3e882fd20688 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L148-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L148-L167

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFppfQuotient_3e882fd20688 (h : IsFppfTorsor G q) : IsFppfQuotient G q := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«FreeQuot».«IsFppfTorsor».«isFppfQuotient» := P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFppfQuotient_3e882fd20688
