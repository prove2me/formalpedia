-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_numericalRadiusBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.numericalRadiusBound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:50:16.505989+00:00
-- url     : https://prove2.me/theorems/6e986120-1334-4674-b1f2-7547f08353a0
-- title:
--   §III.D: C-numerical-radius bound
-- statement:
--   For $N>0$ and arbitrary complex $N$ by $N$ matrices $A,C$, let $r_C(A)=\max_{U\in\mathrm{SU}(N)}|\operatorname{tr}(C^\dagger UAU^\dagger)|$. This maximum is attained, and
--   $$r_C(A)\le\|A\|_F\|C\|_F.$$
--   Equality holds exactly when $UAU^\dagger$ and $C$ are complex linearly dependent for some $U\in\mathrm{SU}(N)$. Linear dependence includes either zero matrix. The norms are Frobenius norms.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 21, §III.D: C-numerical-radius bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- C-numerical-radius bound and equality criterion, PDF p.21. -/
theorem numericalRadiusBound {n : ℕ} (hn : 0 < n) (A C : (Matrix (Fin n) (Fin n) ℂ)) :
    (∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
      numericalRadius A C =
        ‖Matrix.trace (C.conjTranspose * ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose))‖) ∧
    numericalRadius A C ≤ QAlgorithms.frobNorm A * QAlgorithms.frobNorm C ∧
    (numericalRadius A C = QAlgorithms.frobNorm A * QAlgorithms.frobNorm C ↔
      ∃ U : Matrix.specialUnitaryGroup (Fin n) ℂ,
        ComplexCollinear ((U : (Matrix (Fin n) (Fin n) ℂ)) * A * (U : (Matrix (Fin n) (Fin n) ℂ)).conjTranspose) C) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
