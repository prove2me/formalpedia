-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_effCartier_of_forall_mem_6848e920bfed
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_effCartier_of_forall_mem_6848e920bfed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:44:23.445658+00:00
-- url     : https://prove2.me/theorems/0a7639da-5f9a-4493-942c-8449928a5b06
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eff Cartier of forall mem 6848e920bfed: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eff Cartier of forall mem 6848e920bfed
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eff Cartier of forall mem 6848e920bfed construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eff Cartier of forall mem 6848e920bfed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L12-L24

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_effCartier_of_forall_mem_6848e920bfed {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ FinalTheorems.EffCartier (I.comap O.ι)) : FinalTheorems.EffCartier I := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«effCartier_of_forall_mem» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_effCartier_of_forall_mem_6848e920bfed
