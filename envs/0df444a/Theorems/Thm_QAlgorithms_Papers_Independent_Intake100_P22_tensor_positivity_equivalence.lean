-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_tensor_positivity_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.tensor_positivity_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:48:10.694002+00:00
-- url     : https://prove2.me/theorems/ef7c1d93-81aa-4e32-8079-8a8aefe5333b
-- title:
--   Ordinary and fermionic extension positivity coincide
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $E$ be a complex-linear parity-preserving map. On the ordinary two-copy algebra let $E\otimes\mathrm{Id}$ act on the first factor. On disjoint CAR halves define $(E\otimes_f\mathrm{Id})(Z'Z'')=E(Z')Z''$ on ordered monomials, extending linearly. Then
--   $$
--   E\otimes\mathrm{Id}\text{ is positive}\quad\Longleftrightarrow\quad E\otimes_f\mathrm{Id}\text{ is positive}.
--   $$
--   The CAR identification uses $c_a\mapsto c_a\otimes P$ in the first half and $c_{2n+a}\mapsto I\otimes c_a$ in the second, where $P=i^nc_1\cdots c_{2n}$. Neither Gaussianity nor positivity of $E$ is assumed. This transfers the positivity test across the fermionic identification.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 9, Lemma 5: ordinary and fermionic positivity tests coincide

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9-10, Lemma 5: ordinary and fermionic positivity tests coincide
for a complex-linear parity-preserving map. Neither positivity nor Gaussianity
of E is an input hypothesis. -/
theorem tensor_positivity_equivalence {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n))
    (hlinear : ComplexLinear E) (hparity : ParityPreserving s E) :
    PositiveMap (ordinaryExtension E) ↔ PositiveMap (fermionicExtension s E) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
