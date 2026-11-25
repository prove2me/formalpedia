-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_exists_dim_3f23875fc98c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_exists_dim_3f23875fc98c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:12.914165+00:00
-- url     : https://prove2.me/theorems/9a142cd2-8f9d-5be6-94b2-e003fa6ae478
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected exists dim 3f23875fc98c: P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected exists
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected exists dim 3f23875fc98c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected exists dim 3f23875fc98c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L29-L43

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_exists_dim_3f23875fc98c {n : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W.IsPrime) : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IrreducibleBasicOpenConnected».«exists_dim» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_exists_dim_3f23875fc98c
