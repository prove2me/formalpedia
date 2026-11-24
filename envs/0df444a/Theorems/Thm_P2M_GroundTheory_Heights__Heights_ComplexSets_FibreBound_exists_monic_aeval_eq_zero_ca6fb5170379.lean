-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:17.292099+00:00
-- url     : https://prove2.me/theorems/00b9f273-e587-43bc-b0dd-3a16f43eb29f
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists monic aeval eq zero ca6fb5170379: P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists monic aeval eq zero ca6fb51703
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists monic aeval eq zero ca6fb5170379 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists monic aeval eq zero ca6fb5170379 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreBound.lean#L55-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreBound.lean#L55-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379 (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (s : MvPolynomial (Fin n) ℂ ⧸ J) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ),
      g.Monic ∧ g.natDegree ≤ projDegree J A ∧ Polynomial.aeval s g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FibreBound».«exists_monic_aeval_eq_zero» := P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_monic_aeval_eq_zero_ca6fb5170379
