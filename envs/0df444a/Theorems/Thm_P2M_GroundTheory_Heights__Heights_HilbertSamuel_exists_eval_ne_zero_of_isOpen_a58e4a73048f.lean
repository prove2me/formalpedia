-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_eval_ne_zero_of_isOpen_a58e4a73048f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_eval_ne_zero_of_isOpen_a58e4a73048f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:57.010372+00:00
-- url     : https://prove2.me/theorems/27b935d3-39cb-49ef-980e-2600c1fd2e09
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel exists eval ne zero of is Open a58e4a73048f: P2 M Ground Theory Heights  Heights Hilbert Samuel exists eval ne zero of is Open a58e4a73048f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel exists eval ne zero of is Open a58e4a73048f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel exists eval ne zero of is Open a58e4a73048f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PGrowthOffHypersurfacePolynomial.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/PGrowthOffHypersurfacePolynomial.lean#L12-L25

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_eval_ne_zero_of_isOpen_a58e4a73048f {d : ℕ} {Q : MvPolynomial (Fin d) ℂ} (hQ : Q ≠ 0)
    {V : Set (Fin d → ℂ)} (hV : IsOpen V) (hne : V.Nonempty) : ∃ t ∈ V, eval t Q ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«exists_eval_ne_zero_of_isOpen» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_eval_ne_zero_of_isOpen_a58e4a73048f
