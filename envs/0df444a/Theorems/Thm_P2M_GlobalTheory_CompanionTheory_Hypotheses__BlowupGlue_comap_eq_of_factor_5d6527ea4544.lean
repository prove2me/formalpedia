-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_comap_eq_of_factor_5d6527ea4544
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_comap_eq_of_factor_5d6527ea4544
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:43:36.671473+00:00
-- url     : https://prove2.me/theorems/071e3e8c-c4f3-4588-bfed-d54c2ea8f3d7
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Blowup Glue comap eq of factor 5d6527ea4544: P2 M Global Theory Companion Theory Hypotheses  Blowup Glue comap eq of factor 5d6527ea4544
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Blowup Glue comap eq of factor 5d6527ea4544 construction uses the P2 M Global Theory Companion Theory Hypotheses  Blowup Glue comap eq of factor 5d6527ea4544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlowupOfAgreeingIdealCartier.lean#L44-L47

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_comap_eq_of_factor_5d6527ea4544 {T X : Scheme.{0}} {Z Z' : X.IdealSheafData} {O : X.Opens}
    (h : Z'.comap O.ι = Z.comap O.ι) (a : T ⟶ X) (b : T ⟶ O) (hab : b ≫ O.ι = a) : Z'.comap a = Z.comap a := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«BlowupGlue».«comap_eq_of_factor» := P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_comap_eq_of_factor_5d6527ea4544
