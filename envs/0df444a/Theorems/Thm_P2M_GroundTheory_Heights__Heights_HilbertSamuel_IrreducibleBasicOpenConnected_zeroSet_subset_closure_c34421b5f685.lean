-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_zeroSet_subset_closure_c34421b5f685
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_zeroSet_subset_closure_c34421b5f685
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:45.412858+00:00
-- url     : https://prove2.me/theorems/2659899d-d72c-56d6-a6b5-27111bda4ed0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected zero Set subset closure c34421b5f685: P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Conn
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected zero Set subset closure c34421b5f685 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected zero Set subset closure c34421b5f685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L60-L74

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_zeroSet_subset_closure_c34421b5f685 {n d : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hW : W.IsPrime) (hA : ComplexSets.IsFiniteProjection W A)
    {R : MvPolynomial (Fin d) ℂ} (hR : R ≠ 0) :
    ComplexSets.zeroSet W ⊆ closure {x | x ∈ ComplexSets.zeroSet W ∧ eval (A.mulVec x) R ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IrreducibleBasicOpenConnected».«zeroSet_subset_closure» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_zeroSet_subset_closure_c34421b5f685
