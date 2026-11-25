-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_rankAtStalk_eq_one_ac4f75c6d205
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_rankAtStalk_eq_one_ac4f75c6d205
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:15.980227+00:00
-- url     : https://prove2.me/theorems/6dd32cf9-3424-4d39-8f7c-b20b5a9bd772
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of rank At Stalk eq one ac4f75c6d205: P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of rank At Sta
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of rank At Stalk eq one ac4f75c6d205 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over loc Principal of rank At Stalk eq one ac4f75c6d205 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfConormalRankOne.lean#L44-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfConormalRankOne.lean#L44-L140

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOne
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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_rankAtStalk_eq_one_ac4f75c6d205 {A : Type} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent]
    [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I))
    (hP : Module.rankAtStalk I.Cotangent P = 1) :
    LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«locPrincipal_of_rankAtStalk_eq_one» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_rankAtStalk_eq_one_ac4f75c6d205
