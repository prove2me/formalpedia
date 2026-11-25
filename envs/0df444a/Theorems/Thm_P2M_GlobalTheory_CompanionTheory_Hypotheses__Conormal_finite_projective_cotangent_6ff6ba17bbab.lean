-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__Conormal_finite_projective_cotangent_6ff6ba17bbab
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__Conormal_finite_projective_cotangent_6ff6ba17bbab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:31.710139+00:00
-- url     : https://prove2.me/theorems/0c8865c8-703f-42e7-8da6-85c1b6430dba
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Conormal finite projective cotangent 6ff6ba17bbab: P2 M Global Theory Companion Theory Hypotheses  Conormal finite projective cotangent 6ff6ba17bbab
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Conormal finite projective cotangent 6ff6ba17bbab construction uses the P2 M Global Theory Companion Theory Hypotheses  Conormal finite projective cotangent 6ff6ba17bbab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalFiniteProjectiveOfSmooth.lean#L10-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ConormalFiniteProjectiveOfSmooth.lean#L10-L55

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmooth
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
open TensorProduct

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__Conormal_finite_projective_cotangent_6ff6ba17bbab :
    ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth →
      ((Ideal.Quotient.mk I).comp φ).Smooth →
        Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«Conormal».«finite_projective_cotangent» := P2M_GlobalTheory_CompanionTheory_Hypotheses__Conormal_finite_projective_cotangent_6ff6ba17bbab
