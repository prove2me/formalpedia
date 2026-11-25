-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_rankAtStalk_cotangent_eq_one_a658a82d8682
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_rankAtStalk_cotangent_eq_one_a658a82d8682
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:32.245817+00:00
-- url     : https://prove2.me/theorems/a3927e2e-4af5-4106-87d6-f2748fa2d2f9
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over rank At Stalk cotangent eq one a658a82d8682: P2 M Global Theory Companion Theory Hypotheses  Centre Over rank At Stalk cotangent eq one a658
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over rank At Stalk cotangent eq one a658a82d8682 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over rank At Stalk cotangent eq one a658a82d8682 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L60-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L60-L121

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalRankOneOfLocallyPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_rankAtStalk_cotangent_eq_one_a658a82d8682 {A : Type} [CommRing A] [IsDomain A] (I : Ideal A)
    [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent]
    (P : PrimeSpectrum (A ⧸ I))
    (hP : LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I))) :
    Module.rankAtStalk I.Cotangent P = 1 := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«rankAtStalk_cotangent_eq_one» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_rankAtStalk_cotangent_eq_one_a658a82d8682
