-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_bistochastic_diagonal_decomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.bistochastic_diagonal_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:07:38.65301+00:00
-- url     : https://prove2.me/theorems/82a97bd9-0665-4f56-8b9a-eb3233a389bc
-- title:
--   Canonical decomposition into commuting signed elementary maps
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $E$ be a bistochastic completely positive Gaussian map. There are canonical unitaries $V_l,V_r$ and real numbers $b_a$ with $|b_a|\le1$ such that
--   $$
--   E=\operatorname{Ad}_{V_l}\circ\widetilde E\circ\operatorname{Ad}_{V_r},\qquad
--   \widetilde E(c_{a_1}\cdots c_{a_k})=\left(\prod_{j=1}^k b_{a_j}\right)c_{a_1}\cdots c_{a_k}
--   $$
--   for every ordered monomial, including the identity. Here $\operatorname{Ad}_V(X)=VXV^\dagger$. The map $\widetilde E$ is the composition of elementary linear maps, one per $a$, which multiply a monomial containing $c_a$ by $b_a$ and leave every other monomial fixed; these maps pairwise commute. Signed $b_a$ are allowed because both canonical rotations lie in $SO(2n)$. This is the fermionic diagonal contraction decomposition.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 10, §VII: canonical diagonal decomposition of bistochastic CP Gaussian maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.10-11: SO canonical maps on both sides of a signed diagonal
contraction. Elementary maps are specified on all monomials and commute;
they are linear maps, not CAR algebra homomorphisms. -/
theorem bistochastic_diagonal_decomposition {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (hE : GaussianMap s E)
    (hbi : Bistochastic E) (hcp : LinearCompletelyPositive E) :
    ∃ (Vl Vr : Op (Qubits n)) (b : Major n → ℝ), IsCanonicalFLO s Vl ∧ IsCanonicalFLO s Vr ∧
      (∀ a, |b a| ≤ 1) ∧
      E = conjSuperop Vl ∘ diagonalMap s b ∘ conjSuperop Vr ∧
      (∀ A : Finset (Major n), diagonalMap s b (basisOp s A) =
        (∏ a ∈ A, (b a : ℂ)) • basisOp s A) ∧
      diagonalMap s b = elementaryComposition s b ∧
      (∀ a c, elementaryMap s a (b a) ∘ elementaryMap s c (b c) =
        elementaryMap s c (b c) ∘ elementaryMap s a (b a)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
