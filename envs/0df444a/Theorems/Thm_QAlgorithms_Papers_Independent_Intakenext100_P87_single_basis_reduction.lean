-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P87_single_basis_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P87.single_basis_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:15:11.271275+00:00
-- url     : https://prove2.me/theorems/b8d69b7c-a450-46ff-a9b7-0d2c88980dcd
-- title:
--   General common-basis quantum-to-classical reduction
-- statement:
--   Let $\rho$ be a positive semidefinite trace-one operator on a finite-dimensional register, and let $B$ be an orthonormal basis. Consider any finite sequence of observables diagonal in $B$, measured by their spectral projectors with the Lüders rule. Write $\mathcal D_B$ for the complete nonselective measurement in $B$. For every joint outcome string $o$,
--
--   $$\Pr_{\mathcal D_B(\rho)}[o]=\Pr_\rho[o].$$
--
--   Thus the complete joint outcome distribution can be calculated from the classical mixture in $B$. This does not assert equality of conditional postmeasurement states or preservation of fine-grained outcomes outside this common basis.
-- source:
--   Unconditional Security Of Quantum Key Distribution Over Arbitrarily Long Distances, arXiv:quant-ph/9803006v5, PDF p. 4, General common-basis quantum-to-classical reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P87

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P87

open scoped Matrix ComplexConjugate

open QAlgorithms.Measurements

/-- PDF pp.4,10: a common-basis premeasurement preserves the entire joint outcome law. -/
theorem single_basis_reduction {I O : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq O] (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (t : ℕ) (f : Fin t → I → O) (o : Fin t → O) :
    sequentialLaw U (basisPinch U rho) f o = sequentialLaw U rho f o := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P87

end
