-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_flo_simulation_exact
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.flo_simulation_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:10:40.846072+00:00
-- url     : https://prove2.me/theorems/d1eb90f4-d285-4f6f-93c3-874a8b5f0a9f
-- title:
--   Exact finite adaptive FLO simulation by symbol recurrence
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Fix any finite adaptive FLO program. Each unitary step is specified by a real skew $H$ and its supplied rotation $R=e^H\in SO(2n)$, acting quantumly by $e^{i\widehat H}$ from Eq.(4); each occupation measurement has a separate finite continuation for its two outcomes. From an initial Gaussian density with covariance $M$, initialize $f=2^{-n}e^{(i/2)\theta^TM\theta}$. At each unitary update $f$ by the kernel $(0,R^T,0,1)$, and at each outcome update by Eq.(51). Record every intermediate symbol and every branch.
--
--   Let $X_v$ be the corresponding unnormalized quantum branch density and $f_v$ the computed symbol at the same tree node $v$. Then
--   $$
--   \omega(X_v)=f_v,\qquad p_v=\operatorname{Tr}X_v=2^nf_v(0)\ge0,\qquad \sum_{v\text{ terminal}}p_v=1.
--   $$
--   The traces are real. If $p_v=0$, then $X_v=0$. If $p_v>0$, the normalized state is Gaussian and its symbol is $f_v/p_v$. Consequently the terminal weights reproduce the complete outcome distribution and the symbols describe the state at every step. The fixed classical recurrence is independent of the input density apart from its initial covariance. This is a finite exact algebraic simulation statement; no bit encoding, accuracy parameter, or polynomial runtime bound is added.
--
--   For every node the operator is reconstructed as $X_v=\sum_A f_v(A)c_A$, where $A$ ranges over increasing-index supports and $c_A$ is the corresponding ordered Majorana monomial. For $p_v>0$, its normalized covariance has diagonal zero and, for $a\ne b$,
--   $$
--   (M_v)_{ab}=-i\,\operatorname{sgn}(b-a)\frac{f_v(\{a,b\})}{f_v(0)}.
--   $$
--   Thus both the state and its covariance are explicit outputs of the finite recurrence.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 12, §VIII/IX: finite adaptive FLO simulation by Gaussian integrals

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1-2,6,11-12: finite adaptive FLO simulation by the explicit symbol
recurrence, simultaneously at every intermediate node. Computed terminal
weights are exactly Born path probabilities and sum to one; impossible branches
have zero operator and are never normalized. No bit-runtime or polynomial
arithmetic-complexity bound is asserted by this finite exact statement. -/
theorem flo_simulation_exact {n : ℕ} (s : CARSystem n) (P : FLOProgram n)
    (rho : Op (Qubits n)) (M : Matrix (Major n) (Major n) ℝ) (h : StateWith s rho M) :
    let f := ((2 : ℂ) ^ n)⁻¹ • grassExp ((Complex.I / 2) •
      grassQuadratic (M.map Complex.ofReal) (fun a => grassVar (2 * n) a.val))
    let Q := quantumRun s P rho
    let G := symbolicRun P f
    treeMap (majoranaSymbol s) Q = G ∧
      (treeLeaves Q).map (fun X => X.trace.re) = (treeLeaves G).map symbolWeight ∧
      ((treeLeaves G).map symbolWeight).sum = 1 ∧
      (∀ w ∈ (treeLeaves G).map symbolWeight, 0 ≤ w) ∧
      (∀ X ∈ treeValues Q, X = operatorFromSymbol s (majoranaSymbol s X) ∧
        X.trace.im = 0 ∧ 0 ≤ X.trace.re ∧
        (X.trace.re = 0 → X = 0) ∧
        (0 < X.trace.re → FermionicGaussianState s (normalizeComplexTrace X) ∧
          regularCorrelation s (normalizeComplexTrace X) = symbolCorrelation (majoranaSymbol s X) ∧
          ∀ A : Finset (Major n),
            majoranaSymbol s (normalizeComplexTrace X) A = X.trace⁻¹ * majoranaSymbol s X A)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
