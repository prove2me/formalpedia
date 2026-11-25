-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFiniteLocallyFree_55bd9569fe35
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFiniteLocallyFree_55bd9569fe35
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:29.770799+00:00
-- url     : https://prove2.me/theorems/69c767e8-a3dc-4a95-b922-60d707b38351
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Finite Locally Free 55bd9569fe35: P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Finite Locally
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Finite Locally Free 55bd9569fe35 construction uses the P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor is Finite Locally Free 55bd9569fe35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L135-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L135-L146

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFiniteLocallyFree_55bd9569fe35 {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
    (h : IsFppfTorsor G q) (hG : IsFiniteLocallyFree G.hom) : IsFiniteLocallyFree q.left := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«FreeQuot».«IsFppfTorsor».«isFiniteLocallyFree» := P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_isFiniteLocallyFree_55bd9569fe35
