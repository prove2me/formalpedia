-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_surjective_29b40d414390
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_surjective_29b40d414390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:12.670888+00:00
-- url     : https://prove2.me/theorems/13b4a1f2-c54c-4896-8003-62ffe0b7117a
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor surjective 29b40d414390: P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor surjective 29b40d414390
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor surjective 29b40d414390 construction uses the P2 M Global Theory Companion Theory Hypotheses  Free Quot Is Fppf Torsor surjective 29b40d414390 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Algebra₂/RegularHypothesesAndConclusion.lean#L126-L131

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_surjective_29b40d414390 (h : IsFppfTorsor G q) : Surjective q.left := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«FreeQuot».«IsFppfTorsor».«surjective» := P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_surjective_29b40d414390
