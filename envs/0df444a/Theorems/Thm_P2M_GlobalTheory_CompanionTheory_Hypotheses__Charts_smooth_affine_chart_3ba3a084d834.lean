-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__Charts_smooth_affine_chart_3ba3a084d834
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__Charts_smooth_affine_chart_3ba3a084d834
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:21.335446+00:00
-- url     : https://prove2.me/theorems/719d9198-4a73-4dc5-b22e-d7f3ce9811f1
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Charts smooth affine chart 3ba3a084d834: P2 M Global Theory Companion Theory Hypotheses  Charts smooth affine chart 3ba3a084d834
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Charts smooth affine chart 3ba3a084d834 construction uses the P2 M Global Theory Companion Theory Hypotheses  Charts smooth affine chart 3ba3a084d834 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsSmoothAffinePresentationPair.lean#L10-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsSmoothAffinePresentationPair.lean#L10-L30

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPair
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.Charts

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__Charts_smooth_affine_chart_3ba3a084d834 {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k)
    (Z : X.IdealSheafData) (U : X.affineOpens) (hg : Smooth g) (hZ : Smooth (Z.subschemeι ≫ g)) :
    ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«Charts».«smooth_affine_chart» := P2M_GlobalTheory_CompanionTheory_Hypotheses__Charts_smooth_affine_chart_3ba3a084d834
