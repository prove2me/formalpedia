-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_eq_of_isIso_restrict_34b16c549938
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_eq_of_isIso_restrict_34b16c549938
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:49.337064+00:00
-- url     : https://prove2.me/theorems/6eac79ec-bef3-4cd8-996f-feb34464f6ed
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eq of is Iso restrict 34b16c549938: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eq of is Iso restrict 34b16c549938
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eq of is Iso restrict 34b16c549938 construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue eq of is Iso restrict 34b16c549938 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L37-L42

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_eq_of_isIso_restrict_34b16c549938 {X X' T : Scheme.{0}} {π : X' ⟶ X} {O : X.Opens} [IsIso (π ∣_ O)] (s : T ⟶ X')
    (c : T ⟶ O) (h : c ≫ O.ι = s ≫ π) : s = c ≫ inv (π ∣_ O) ≫ (π ⁻¹ᵁ O).ι := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«eq_of_isIso_restrict» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_eq_of_isIso_restrict_34b16c549938
