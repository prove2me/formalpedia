-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_tetrahedral_extreme_channels
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.tetrahedral_extreme_channels
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:18:04.26929+00:00
-- url     : https://prove2.me/theorems/7b7f17a5-52a7-42a6-a509-edbb120a215e
-- title:
--   Example 23: explicit Pauli corner and all extreme tetrahedral channels
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. The normalized, reference-first Choi operator is $c_T=(\mathrm{id}_{d_1}\otimes T)(|\Omega\rangle\langle\Omega|)$, where $|\Omega\rangle=d_1^{-1/2}\sum_i|i,i\rangle$, with two input-sized factors before $T$ acts. Use the concrete tetrahedral representation on $H$ above and its real orthonormal coordinates. The source unitary $V$ is fixed by the four displayed images of tetrahedron vertices on page 13; in these coordinates it is $\operatorname{diag}(1,\zeta,\zeta^2)$. Put $T_j(A)=V^jA(V^j)^*$ for $j=0,1,2$, let $F$ be swap, and let $P=I-\sum_j c_{T_j}$. This is a rank-six orthogonal projector. Define $X=PF$, $Y=PF(2V\otimes V^*+I)/\sqrt3$, and $Z=P(2V\otimes V^*+I)/(i\sqrt3)$. These Hermitian operators are supported in the actual commutant corner and satisfy $V_iV_j+V_jV_i=2\delta_{ij}P$ for $(V_x,V_y,V_z)=(X,Y,Z)$. They and $P$ span that corner. Its density operators are precisely
--
--   $$J_\lambda=\frac{P+\lambda_xX+\lambda_yY+\lambda_zZ}{6},\qquad\lambda\in\mathbb R^3,\quad\sum_i\lambda_i^2\le1.$$
--
--   All these are channel Choi states. The extreme covariant channels are exactly the three $T_j$ (Choi rank one) and the channels with Choi state $J_\lambda$ for $\sum_i\lambda_i^2=1$ (Choi rank three). The Werner–Holevo channel $A\mapsto(\operatorname{tr}(A)I-A^T)/2$, attributed to [43], is $J_{(-1,0,0)}$. The Bloch equivalence is restricted to density matrices, correcting the literal algebra-only wording.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 13, Example 23: explicit Pauli corner and all extreme tetrahedral channels

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P21.tetraTopology

/-- PDF pp.13--14, Example 23: the concrete Pauli corner and every extreme
channel. The Bloch iff is restricted to density matrices, repairing the printed
J-in-algebra iff statement, whose literal version incorrectly includes zero.
Werner--Holevo's channel is the lambda=(-1,0,0) point. -/
theorem tetrahedral_extreme_channels :
    tetraVᴴ * tetraV = 1 ∧ tetraV * tetraVᴴ = 1 ∧
    tetraCornerProjection.IsHermitian ∧
    tetraCornerProjection * tetraCornerProjection = tetraCornerProjection ∧
    tetraCornerProjection.rank = 6 ∧
    (∀ j, (tetraPauli j).IsHermitian ∧ tetraPauli j ∈ tetraCorner) ∧
    (∀ i j, tetraPauli i * tetraPauli j + tetraPauli j * tetraPauli i =
      if i = j then 2 • tetraCornerProjection else 0) ∧
    tetraCorner = ((Submodule.span ℂ
      {tetraCornerProjection, tetraPauli 0, tetraPauli 1, tetraPauli 2}) :
        Set (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ)) ∧
    (∀ J, (J ∈ tetraCorner ∧ IsDensityMatrix J) ↔
      ∃ lambda : Fin 3 → ℝ, (∑ j, lambda j ^ 2) ≤ 1 ∧ J = tetraBloch lambda) ∧
    (∀ lambda : Fin 3 → ℝ, (∑ j, lambda j ^ 2) ≤ 1 →
      ∃ T ∈ tetraClass, normalizedChoi T = tetraBloch lambda) ∧
    (∀ T ∈ tetraClass, T ∈ tetraClass.extremePoints ℝ ↔
      (∃ j : Fin 3, T = tetraUnitary j) ∨
      (∃ lambda : Fin 3 → ℝ, (∑ j, lambda j ^ 2) = 1 ∧
        normalizedChoi T = tetraBloch lambda)) ∧
    (∀ j, tetraUnitary j ∈ tetraClass.extremePoints ℝ ∧
      (normalizedChoi (tetraUnitary j)).rank = 1) ∧
    (∀ lambda : Fin 3 → ℝ, (∑ j, lambda j ^ 2) = 1 →
      (tetraBloch lambda).rank = 3) ∧
    normalizedChoi (wernerHolevo 3) = tetraBloch ![-1, 0, 0] := by sorry

end QAlgorithms.Papers.Independent.Extend50.P21

end
