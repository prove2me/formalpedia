-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_gen_of_map_eq_span_8fb85a512b0b
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_gen_of_map_eq_span_8fb85a512b0b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:56.957038+00:00
-- url     : https://prove2.me/theorems/b96d567d-3351-48e3-a8b1-e29f22178267
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Centre Over exists gen of map eq span 8fb85a512b0b: P2 M Global Theory Companion Theory Hypotheses  Centre Over exists gen of map eq span 8fb85a512b0b
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Centre Over exists gen of map eq span 8fb85a512b0b construction uses the P2 M Global Theory Companion Theory Hypotheses  Centre Over exists gen of map eq span 8fb85a512b0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfCartierAt.lean#L13-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocallyPrincipalOfCartierAt.lean#L13-L42

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAt
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_gen_of_map_eq_span_8fb85a512b0b {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (t : A)
    [IsLocalization.Away t B] (I : Ideal A) (b : B) (hb : b ≠ 0)
    (hI : I.map (algebraMap A B) = Ideal.span {b}) :
    ∃ f ∈ I, f ≠ 0 ∧ ∀ g ∈ I, ∃ n : ℕ, t ^ n * g ∈ Ideal.span {f} := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CentreOver».«exists_gen_of_map_eq_span» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_gen_of_map_eq_span_8fb85a512b0b
