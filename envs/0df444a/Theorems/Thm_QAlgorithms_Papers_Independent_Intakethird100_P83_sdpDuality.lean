-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_sdpDuality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.sdpDuality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:08:18.049062+00:00
-- url     : https://prove2.me/theorems/2a4660a9-17bb-43d9-968e-e271f208fbee
-- title:
--   Three attained SDP characterizations of W
-- statement:
--   Let $\rho$ be any normalized bipartite state on nonzero finite-dimensional spaces, and let $T_B$ denote ordinary partial transpose on Bob. All operator inequalities are Loewner inequalities, $\|\cdot\|_\infty$ is the largest singular value, and $\|\cdot\|_1$ is the trace norm. The following three optimization problems have the same value and each attains its optimum:
--
--   $$\begin{aligned}W(\rho)&=\max_{R=R^\dagger}\{\operatorname{Re}\operatorname{Tr}(T_B(\rho)R):\|R\|_\infty\le1,\ T_B(R)\ge0\}\\&=\min_{U,V\ge0}\{\operatorname{Re}\operatorname{Tr}(U+V):T_B(U-V)\ge\rho\}\\&=\min_{X\ge\rho}\|T_B(X)\|_1.\end{aligned}$$
--
--   These are explicit finite-dimensional SDPs. The first witness need not be positive, and the last variable is not constrained to have trace one.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 2, Unnumbered result: equivalent attained SDPs (7)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Strong duality and attained equivalent SDPs (7)–(9), PDF p.2.
R need not be positive and X need not have trace one. -/
theorem sdpDuality [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    wValue rho = dualUVValue rho ∧ wValue rho = dualXValue rho ∧
    (∃ R, WFeasible R ∧ effectProb (partialTranspose rho) R = wValue rho) ∧
    (∃ U V, DualUVFeasible rho U V ∧ (U + V).trace.re = dualUVValue rho) ∧
    (∃ X, Loewner rho X ∧ traceNorm (partialTranspose X) = dualXValue rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
