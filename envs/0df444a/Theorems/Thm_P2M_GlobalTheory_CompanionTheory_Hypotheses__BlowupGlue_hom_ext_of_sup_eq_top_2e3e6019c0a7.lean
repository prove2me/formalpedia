-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_hom_ext_of_sup_eq_top_2e3e6019c0a7
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_hom_ext_of_sup_eq_top_2e3e6019c0a7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:23.572903+00:00
-- url     : https://prove2.me/theorems/25a0b1dd-e259-54d8-a37b-63862881b5f7
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue hom ext of sup eq top 2e3e6019c0a7: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue hom ext of sup eq top 2e3e6019c0a7
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue hom ext of sup eq top 2e3e6019c0a7 construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue hom ext of sup eq top 2e3e6019c0a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L77-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L77-L86

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_hom_ext_of_sup_eq_top_2e3e6019c0a7 {W Y : Scheme.{0}} (W₁ W₂ : W.Opens) (h : W₁ ⊔ W₂ = ⊤) (s t : W ⟶ Y)
    (h₁ : W₁.ι ≫ s = W₁.ι ≫ t) (h₂ : W₂.ι ≫ s = W₂.ι ≫ t) : s = t := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«hom_ext_of_sup_eq_top» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_hom_ext_of_sup_eq_top_2e3e6019c0a7
