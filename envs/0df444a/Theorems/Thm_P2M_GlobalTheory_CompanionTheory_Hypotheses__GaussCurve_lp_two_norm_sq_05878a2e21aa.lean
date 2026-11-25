-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_lp_two_norm_sq_05878a2e21aa
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_lp_two_norm_sq_05878a2e21aa
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:46.939291+00:00
-- url     : https://prove2.me/theorems/d3799d6f-1e98-4102-a253-106cc911ba62
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Gauss Curve lp two norm sq 05878a2e21aa: P2 M Global Theory Companion Theory Hypotheses  Gauss Curve lp two norm sq 05878a2e21aa
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Gauss Curve lp two norm sq 05878a2e21aa construction uses the P2 M Global Theory Companion Theory Hypotheses  Gauss Curve lp two norm sq 05878a2e21aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HasDerivAtLpOfDominated.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HasDerivAtLpOfDominated.lean#L16-L20

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_lp_two_norm_sq_05878a2e21aa {E : Type*} [MeasurableSpace E] {μ : Measure E} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«GaussCurve».«lp_two_norm_sq» := P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_lp_two_norm_sq_05878a2e21aa
