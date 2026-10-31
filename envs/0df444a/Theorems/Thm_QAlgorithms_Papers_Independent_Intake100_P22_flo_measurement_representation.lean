-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_flo_measurement_representation
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.flo_measurement_representation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:32:21.284141+00:00
-- url     : https://prove2.me/theorems/812070c2-0b7c-40fd-a69e-c83337b35b42
-- title:
--   Occupation projectors have the FLO Gaussian integral representation
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For a mode $1\le j\le n$ and outcome $\epsilon\in\{0,1\}$, put $P_{j,0}=a_ja_j^\dagger$, $P_{j,1}=a_j^\dagger a_j$ and $E_{j,\epsilon}(X)=P_{j,\epsilon}XP_{j,\epsilon}$. Write $\sum_a'$ for the sum excluding $2j-1,2j$, and set
--   $$
--   S_{j,\epsilon}(\theta,\eta)=i(-1)^\epsilon(\theta_{2j-1}\theta_{2j}-\eta_{2j-1}\eta_{2j})+i\sum_a'\theta_a\eta_a.
--   $$
--   Then $E_{j,\epsilon}$ is Gaussian and, for every operator $X$,
--   $$
--   \omega(E_{j,\epsilon}(X),\theta)=\frac12\int e^{S_{j,\epsilon}(\theta,\eta)+i\eta^T\mu}\omega(X,\mu)\,D\eta\,D\mu.
--   $$
--   For a Gaussian input density, division of the output by its positive outcome trace gives a Gaussian density. This supplies the measurement part of the Lagrangian FLO representation.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 11, §VIII, Eq.(51): Lagrangian FLO measurement representation (seed paper result)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.11, Eq.(51): both occupation projectors have the stated Lagrangian
kernel on all operators. The source's phrase "Gaussian state" for the output
requires division by the positive outcome trace. -/
theorem flo_measurement_representation {n : ℕ} (s : CARSystem n) (j : Fin n)
    (outcome : Bool) :
    GaussianMap s (conjSuperop (modeProjector s j outcome)) ∧
    (∀ X : Op (Qubits n), majoranaSymbol s (conjSuperop (modeProjector s j outcome) X) =
      measurementEval j outcome (majoranaSymbol s X)) ∧
    (∀ rho : Op (Qubits n), FermionicGaussianState s rho →
      let Y := conjSuperop (modeProjector s j outcome) rho
      0 < Y.trace.re → FermionicGaussianState s (normalizeComplexTrace Y)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
