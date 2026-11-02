-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_projectorLowerBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.projectorLowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:17:54.081832+00:00
-- url     : https://prove2.me/theorems/43ff4653-5239-419e-9eb5-b60fa6347670
-- title:
--   A lower bound from the actual support projector
-- statement:
--   Let $\rho$ be a positive semidefinite, trace-one bipartite operator on arbitrary nonzero finite-dimensional local spaces, and let $P_\rho$ be the orthogonal projector onto its positive spectral support. The one-copy deterministic PPT rate $E_1$, defined using positive real target sizes, satisfies
--
--   $$E_1(\rho)\ge-\log_2\|T_B(P_\rho)\|_\infty.$$
--
--   The projector is nonzero, so its partial-transpose norm is positive. The displayed lower bound is not truncated at zero and may be negative.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 5, Unnumbered consequence of (15): support-projector lower bound

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

/-- Consequence of (15), PDF p.5. The projector is constructed from rho;
the lower bound can be negative and is not truncated at zero. -/
theorem projectorLowerBound [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    -Real.logb 2 (complexSpectralNorm (partialTranspose (supportProjector rho))) ≤ oneCopyExact rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
