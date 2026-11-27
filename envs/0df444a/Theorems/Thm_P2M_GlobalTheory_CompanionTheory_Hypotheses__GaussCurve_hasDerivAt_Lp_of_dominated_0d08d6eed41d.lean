-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_hasDerivAt_Lp_of_dominated_0d08d6eed41d
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_hasDerivAt_Lp_of_dominated_0d08d6eed41d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:36.722996+00:00
-- url     : https://prove2.me/theorems/f1c442c3-bcb4-5296-93b2-26122d7da878
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Gauss Curve has Deriv At Lp of dominated 0d08d6eed41d: P2 M Global Theory Companion Theory Hypotheses  Gauss Curve has Deriv At Lp of dominated 0d08d6ee
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Gauss Curve has Deriv At Lp of dominated 0d08d6eed41d construction uses the P2 M Global Theory Companion Theory Hypotheses  Gauss Curve has Deriv At Lp of dominated 0d08d6eed41d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HasDerivAtLpOfDominated.lean#L22-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HasDerivAtLpOfDominated.lean#L22-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RealMpData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HasDerivAtLpOfDominated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.CompanionTheory.Hypotheses₂ Filter Topology
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_hasDerivAt_Lp_of_dominated_0d08d6eed41d {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (F : ℝ → Lp ℂ 2 μ) (G : Lp ℂ 2 μ) (f f' : ℝ → E → ℂ) (b : E → ℝ) (t₀ δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ t, F t =ᵐ[μ] f t) (hG : G =ᵐ[μ] f' t₀) (hb : MemLp b 2 μ)
    (hd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, HasDerivAt (fun s => f s x) (f' t x) t)
    (hbd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, ‖f' t x‖ ≤ b x) :
    HasDerivAt F G t₀ := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«GaussCurve».«hasDerivAt_Lp_of_dominated» := P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_hasDerivAt_Lp_of_dominated_0d08d6eed41d
