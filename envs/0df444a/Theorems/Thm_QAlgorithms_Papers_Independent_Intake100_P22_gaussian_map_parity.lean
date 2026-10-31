-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_map_parity
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_map_parity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:43:23.622723+00:00
-- url     : https://prove2.me/theorems/a63868b9-32d4-41a1-9334-984e1ab7727b
-- title:
--   Gaussian maps preserve both parity sectors
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For any Gaussian map $E$, even and odd operators remain in their respective sectors:
--   $$
--   X\text{ even}\Rightarrow E(X)\text{ even},\qquad
--   X\text{ odd}\Rightarrow E(X)\text{ odd}.
--   $$
--   Each sector is defined by the degrees of the ordered Majorana expansion. Positivity and trace preservation are not required. This allows the fermionic map calculus to retain information on the entire operator algebra.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 8, Lemma 3: Gaussian maps preserve parity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma 3: preservation of both parity sectors. -/
theorem gaussian_map_parity {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (hE : GaussianMap s E) :
    ParityPreserving s E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
