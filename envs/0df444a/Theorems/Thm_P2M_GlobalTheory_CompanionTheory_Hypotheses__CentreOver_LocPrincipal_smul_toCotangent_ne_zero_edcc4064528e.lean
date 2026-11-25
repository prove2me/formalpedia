-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_smul_toCotangent_ne_zero_edcc4064528e
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_smul_toCotangent_ne_zero_edcc4064528e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:15.18742+00:00
-- url     : https://prove2.me/theorems/adf78670-5ded-4146-a91e-acf3a3837870
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal smul to Cotangent ne zero edcc4064528e: P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal smul to Cota
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal smul to Cotangent ne zero edcc4064528e construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over Loc Principal smul to Cotangent ne zero edcc4064528e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalRankOneOfLocallyPrincipal.lean#L28-L46

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_smul_toCotangent_ne_zero_edcc4064528e {A : Type} [CommRing A] [IsDomain A] {I p : Ideal A}
    [p.IsPrime] (hIp : I ≤ p) {t f : A} (ht : t ∉ p) (hf : f ∈ I) (hf0 : f ≠ 0)
    (h : ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f}) {s : A} (hs : s ∉ p) :
    s • I.toCotangent ⟨f, hf⟩ ≠ 0 := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«LocPrincipal».«smul_toCotangent_ne_zero» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_LocPrincipal_smul_toCotangent_ne_zero_edcc4064528e
