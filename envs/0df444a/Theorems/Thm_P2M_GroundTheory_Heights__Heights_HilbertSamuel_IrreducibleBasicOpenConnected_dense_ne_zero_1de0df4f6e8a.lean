-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_dense_ne_zero_1de0df4f6e8a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_dense_ne_zero_1de0df4f6e8a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:27.117825+00:00
-- url     : https://prove2.me/theorems/c576a181-4a28-5f9c-aae4-38a462716969
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected dense ne zero 1de0df4f6e8a: P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected dens
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected dense ne zero 1de0df4f6e8a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected dense ne zero 1de0df4f6e8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L45-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps
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
open MvPolynomial Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_dense_ne_zero_1de0df4f6e8a {d : ℕ} {R : MvPolynomial (Fin d) ℂ} (hR : R ≠ 0) :
    Dense {y : Fin d → ℂ | eval y R ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IrreducibleBasicOpenConnected».«dense_ne_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_dense_ne_zero_1de0df4f6e8a
