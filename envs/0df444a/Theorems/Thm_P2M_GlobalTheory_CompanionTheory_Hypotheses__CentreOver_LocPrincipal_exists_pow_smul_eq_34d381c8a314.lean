-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_smul_eq_34d381c8a314
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_smul_eq_34d381c8a314
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:09.746472+00:00
-- url     : https://prove2.me/theorems/c33879bd-495e-43e2-b4b7-0408931d717a
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow smul eq 34d381c8a314: P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow smul eq
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow smul eq 34d381c8a314 construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal exists pow smul eq 34d381c8a314 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L48-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L48-L58

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_smul_eq_34d381c8a314 {A : Type} [CommRing A] {I : Ideal A} {t f : A}
    (hf : f ∈ I) (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) (m : I.Cotangent) :
    ∃ (n : ℕ) (c : A), t ^ n • m = c • I.toCotangent ⟨f, hf⟩ := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«LocPrincipal».«exists_pow_smul_eq» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_exists_pow_smul_eq_34d381c8a314
