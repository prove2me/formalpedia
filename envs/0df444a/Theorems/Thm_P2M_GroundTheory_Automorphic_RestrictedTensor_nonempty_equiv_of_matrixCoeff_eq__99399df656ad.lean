-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad
-- name    : P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:13.31262+00:00
-- url     : https://prove2.me/theorems/9c7a3d89-e14c-4d3b-933e-8be61d775de5
-- title:
--   P2 M Ground Theory Automorphic Restricted Tensor nonempty equiv of matrix Coeff eq  99399df656ad: P2 M Ground Theory Automorphic Restricted Tensor nonempty equiv of matrix Coeff eq  99399df656ad
-- statement:
--   The P2 M Ground Theory Automorphic Restricted Tensor nonempty equiv of matrix Coeff eq  99399df656ad construction uses the P2 M Ground Theory Automorphic Restricted Tensor nonempty equiv of matrix Coeff eq  99399df656ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L76-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GenWindow.lean#L76-L126

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

theorem P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad {ρ : Representation ℂ M V} {σ : Representation ℂ M W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Dual ℂ V} {w : W} {m : Dual ℂ W}
    (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) : Nonempty (ρ.Equiv σ) := by sorry

alias «GroundTheory».«Automorphic».«RestrictedTensor».«nonempty_equiv_of_matrixCoeff_eq'» := P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad
