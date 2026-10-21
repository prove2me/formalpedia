-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P01_generallyCoupled_normalized_and_M_orthogonal
-- name    : QAlgorithms.Papers.Independent.Renew46.P01.generallyCoupled_normalized_and_M_orthogonal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:41:30.416993+00:00
-- url     : https://prove2.me/theorems/47db1c7f-9d5b-4c21-b82c-cda31e87ab39
-- title:
--   General coupling preserves normalization and orthogonality in M
-- statement:
--   Fix a finite rooted coupling tree, a finite arity bound $K$, and all its $J$ and internal $j$ labels. Each internal vertex has between two and $K$ children. Each leaf is a finite-dimensional qudit with an orthonormal family of admissible base vectors. At each vertex, fix coefficients with finite admissible child and parent label domains, satisfying (GC1) and (GC2). Thus, at fixed $J,j$, the coefficient rows are orthonormal in the parent label $M$.
--
--   Let $\psi_M$ be the vector obtained by recursively expanding each vertex according to equation (33), and let $X$ be the computational configuration space of all leaves. For all admissible root labels $M,N$,
--
--   $$
--   \langle\psi_M\mid\psi_N\rangle
--   =\sum_{x\in X}\overline{\psi_M(x)}\psi_N(x)=\delta_{M,N},
--   \qquad \|\psi_M\|_2=1.
--   $$
--
--   This ensures that recursive general coupling produces quantum states. It asserts orthogonality in $M$ at fixed vertex data, without asserting orthogonality between different $J$ labels or a complete basis.
-- source:
--   Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform, arXiv:2305.04069v3, PDF p. 13, §IV.A, unnumbered: generally coupled states are normalized and M-orthogonal

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF pp.12--13, §IV.A, (32)--(33): generally coupled states are
orthonormal in admissible M, at fixed vertex coefficients and J,j labels,
and each is a unit vector. No orthogonality between different J is claimed. -/
theorem generallyCoupled_normalized_and_M_orthogonal
    (K : ℕ) (t : CouplingTree) (A : CouplingData t) (h : CouplingValid t A K) :
    (∀ M N : Fin t.rootDim,
      (∑ x : t.Config, star (coupledAmplitude t A M x) * coupledAmplitude t A N x) =
        if M = N then 1 else 0) ∧
      (∀ M : Fin t.rootDim, IsState (coupledState t A M)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P01

end
