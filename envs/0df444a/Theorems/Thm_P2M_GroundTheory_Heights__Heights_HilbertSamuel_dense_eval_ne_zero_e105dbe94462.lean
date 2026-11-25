-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_dense_eval_ne_zero_e105dbe94462
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_dense_eval_ne_zero_e105dbe94462
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:49.162994+00:00
-- url     : https://prove2.me/theorems/bb62a115-cbf7-4c79-9593-9104a40b3d14
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel dense eval ne zero e105dbe94462: P2 M Ground Theory Heights  Heights Hilbert Samuel dense eval ne zero e105dbe94462
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel dense eval ne zero e105dbe94462 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel dense eval ne zero e105dbe94462 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PGrowthOffHypersurfacePolynomial.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PGrowthOffHypersurfacePolynomial.lean#L27-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StEntirePolynomialGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PGrowthOffHypersurfacePolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_dense_eval_ne_zero_e105dbe94462 {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0) :
    Dense {y : Fin d → ℂ | eval y Q ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«dense_eval_ne_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_dense_eval_ne_zero_e105dbe94462
