-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_isIso_restrict_of_effCartier_2d1d8fd7dfd7
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_isIso_restrict_of_effCartier_2d1d8fd7dfd7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:04.767848+00:00
-- url     : https://prove2.me/theorems/4d89af97-144d-57eb-a434-eac17a0daa29
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue is Iso restrict of eff Cartier 2d1d8fd7dfd7: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue is Iso restrict of eff Cartier 2d1d
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue is Iso restrict of eff Cartier 2d1d8fd7dfd7 construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue is Iso restrict of eff Cartier 2d1d8fd7dfd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L26-L35

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_isIso_restrict_of_effCartier_2d1d8fd7dfd7 {X X' : Scheme.{0}} {π : X' ⟶ X} {J : X.IdealSheafData} (h : FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : FinalTheorems.EffCartier (J.comap U.ι)) : IsIso (π ∣_ U) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«isIso_restrict_of_effCartier» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_isIso_restrict_of_effCartier_2d1d8fd7dfd7
