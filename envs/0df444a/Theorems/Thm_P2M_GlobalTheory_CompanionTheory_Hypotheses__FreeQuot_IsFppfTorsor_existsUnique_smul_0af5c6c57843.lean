-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_existsUnique_smul_0af5c6c57843
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_existsUnique_smul_0af5c6c57843
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:46.867529+00:00
-- url     : https://prove2.me/theorems/1d45785a-a0b2-4fc4-93ec-5e99046d9a8d
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor exists Unique smul 0af5c6c57843: P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor exists Unique smul 0a
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor exists Unique smul 0af5c6c57843 construction uses the P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor exists Unique smul 0af5c6c57843 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L87-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L87-L101

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_existsUnique_smul_0af5c6c57843 (h : IsFppfTorsor G q) {T : Over S} (x y : T ⟶ X) (e : y ≫ q = x ≫ q) :
    ∃! g : T ⟶ G, g • x = y := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«FreeQuot».«IsFppfTorsor».«existsUnique_smul» := P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_existsUnique_smul_0af5c6c57843
