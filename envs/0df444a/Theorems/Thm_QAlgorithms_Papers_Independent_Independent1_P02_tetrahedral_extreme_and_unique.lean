-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P02_tetrahedral_extreme_and_unique
-- name    : QAlgorithms.Papers.Independent.Independent1.P02.tetrahedral_extreme_and_unique
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:18:59.625019+00:00
-- url     : https://prove2.me/theorems/6095ade9-3211-4fb1-928d-c81ab594620c
-- title:
--   Section 3 Counterexample, Eq.(19): qutrit extreme EBT channel not CQ
-- statement:
--   Fix an orthonormal basis $e_0,e_1,e_2$ of $\mathbb C^3$. Let $v_0=(e_0+e_1+e_2)/\sqrt3$, $v_1=(e_0-e_1-e_2)/\sqrt3$, $v_2=(-e_0+e_1-e_2)/\sqrt3$, and $v_3=(-e_0-e_1+e_2)/\sqrt3$. The computed channel
--
--   $$\Phi(X)=\tfrac34\sum_{i=0}^3\operatorname{Tr}(|v_i\rangle\langle v_i|X)|v_i\rangle\langle v_i|$$
--
--   is extreme in EBT, is not CQ, and is not extreme in CPT. Its distinct rays have overlap $-1/3$, and the only Hermitian projections commuting with all four pure densities are $0,I$, ruling out an orthogonal block split.
--
--   Its positive rank-one Holevo form is essentially unique: in any finite representation with strictly positive weights $a_k$, unit output vectors $y_k$, and unit input vectors $z_k$, each pair of pure densities equals $(|v_i\rangle\langle v_i|,|v_i\rangle\langle v_i|)$ for some $i$. The sum of weights belonging to each ray is $3/4$. This permits splitting and merging weights and arbitrary vector phases; it makes no assertion about arbitrary mixed-output or zero-effect presentations.
--
--   For each i, the plane reflection U_i=I-2|v_i⟩⟨v_i| is unitary, and on every operator X the final page-12 construction is explicitly realized by Phi(X)=(1/4)X+(3/16) sum_(i=0)^3 U_i X U_i†. The five nonnegative coefficients sum to one.
-- source:
--   General Entanglement Breaking Channels, arXiv:quant-ph/0302031v2, Section 3 Counterexample, Eq.(19): qutrit extreme EBT channel not CQ, PDF p. 11. https://arxiv.org/abs/quant-ph/0302031v2 . PDF SHA-256: b9741af8740a74b5771c71520597f0a6ee2fa27a7ab56de59ddd399c4f49c465.

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

/-!
# Entanglement Breaking Channels (quant-ph/0302031v2)

All reference factors occur first. General EB uses the separable positive cone;
EBT additionally preserves trace. Proposed source corrections below require
independent source moderation; see MODERATION_NOTES.md in the assigned unit.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

































































/-- Eq.(19), PDF pp.11–12: EBT extremality, non-CQ, non-CPT-extremality,
and essential uniqueness of positive normalized rank-one presentations.
The final p.12 reflection mixture is included with identity weight 1/4 and
weight 3/16 on each of the four plane reflections. Vector phases and split
weights are allowed. No nontrivial orthogonal block
split is encoded by the common projectors of the four output rays. -/
theorem tetrahedral_extreme_and_unique (e : OrthonormalBasis (Fin 3) ℂ (StateVector 3)) :
    tetrahedralEndomorphism e ∈ (ebtSet 3).extremePoints ℝ ∧
    ¬ IsCQ (tetrahedralEndomorphism e) ∧
    tetrahedralEndomorphism e ∉ (cptSet 3).extremePoints ℝ ∧
    (∀ i : Fin 4, (1 - (2 : ℂ) • pureDensity (tetrahedralVectors e i)) ∈
      Matrix.unitaryGroup (Fin 3) ℂ) ∧
    (∀ X : Algebra 3, tetrahedralEndomorphism e X = (1/4 : ℂ) • X +
      (3/16 : ℂ) • ∑ i : Fin 4,
        conjSuperop (1 - (2 : ℂ) • pureDensity (tetrahedralVectors e i)) X) ∧
    (∀ i j : Fin 4, i ≠ j → inner ℂ (tetrahedralVectors e i) (tetrahedralVectors e j) = (-1/3 : ℂ)) ∧
    (∀ Q : Algebra 3, Q.IsHermitian → Q*Q = Q →
      (∀ i, Q*pureDensity (tetrahedralVectors e i) = pureDensity (tetrahedralVectors e i)*Q) →
      Q = 0 ∨ Q = 1) ∧
    (∀ (m : ℕ) (weights : Fin m → ℝ) (y z : Fin m → StateVector 3),
      (∀ k, 0 < weights k) → (∀ k, IsState (y k) ∧ IsState (z k)) →
      tetrahedralEndomorphism e = Entanglement.holevoMap (fun k => pureDensity (y k))
        (fun k => (weights k : ℂ) • pureDensity (z k)) →
      (∀ k, ∃ i : Fin 4, pureDensity (y k) = pureDensity (tetrahedralVectors e i) ∧
        pureDensity (z k) = pureDensity (tetrahedralVectors e i)) ∧
      ∀ i : Fin 4, (∑ k ∈ Finset.univ.filter (fun k =>
        pureDensity (y k) = pureDensity (tetrahedralVectors e i)), weights k) = 3/4) := by sorry




end QAlgorithms.Papers.Independent.Independent1.P02
