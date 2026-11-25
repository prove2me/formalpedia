-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_mul_sq_66e694ab0060
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_mul_sq_66e694ab0060
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:18.552798+00:00
-- url     : https://prove2.me/theorems/954d81fb-3332-4dc8-90dc-7e409c56323a
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow mul sq 66e694ab0060: P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow mul sq 66
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow mul sq 66e694ab0060 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow mul sq 66e694ab0060 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L10-L26

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_mul_sq_66e694ab0060 {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {x : A} (hx : x ∈ I ^ 2) :
    ∃ N : ℕ, ∃ c : A, t ^ N * x = c * (f * f) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«LocPrincipal».«exists_pow_mul_sq» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_mul_sq_66e694ab0060
