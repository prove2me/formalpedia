-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_generator_of_rankAtStalk_eq_one_fad9a8a39d3b
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_generator_of_rankAtStalk_eq_one_fad9a8a39d3b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:45.308129+00:00
-- url     : https://prove2.me/theorems/3a26064d-1194-4c7a-b737-25fe80dc0ff6
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over exists generator of rank At Stalk eq one fad9a8a39d3b: P2 M Global Theory Companion Theory Hypotheses  Centre Over exists generator of rank
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over exists generator of rank At Stalk eq one fad9a8a39d3b construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over exists generator of rank At Stalk eq one fad9a8a39d3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfConormalRankOne.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfConormalRankOne.lean#L10-L42

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_generator_of_rankAtStalk_eq_one_fad9a8a39d3b {B M : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] [Module.Projective B M] (P : PrimeSpectrum B)
    (h : Module.rankAtStalk M P = 1) :
    ∃ m : M, ∀ x : M, ∃ s : B, s ∉ P.asIdeal ∧ ∃ b : B, s • x = b • m := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«exists_generator_of_rankAtStalk_eq_one» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_generator_of_rankAtStalk_eq_one_fad9a8a39d3b
