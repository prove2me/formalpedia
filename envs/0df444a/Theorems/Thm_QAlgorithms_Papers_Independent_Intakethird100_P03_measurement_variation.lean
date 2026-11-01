-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_measurement_variation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.measurement_variation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:54:52.592196+00:00
-- url     : https://prove2.me/theorems/713dc184-056d-4777-bf6c-3d80f219a8e6
-- title:
--   Lemma 4: measurement variation bounded by trace norm
-- statement:
--   Let $\Omega$ be a finite family of mutually orthogonal subspaces of a finite complex Hilbert space, and let $\rho,\gamma$ be density operators. With $P(\rho,V)=\operatorname{Tr}(\rho\Pi_V)$,
--
--   $$
--   \sum_{V\in\Omega}|P(\rho,V)-P(\gamma,V)|\le\|\rho-\gamma\|_{\mathrm{tr}}.
--   $$
--
--   The family need not span the Hilbert space. The sum is the unhalved variation expression used in the paper.
--
--   This bounds measurement errors even when the observable can have no value.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 12, Lemma 4: measurement variation bounded by trace norm

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Lemma 4: sum of absolute probability differences for a possibly
incomplete orthogonal family; this is not half-normalized total variation. -/
theorem measurement_variation {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) (O : OrthogonalProjectorFamily I r) (rho gamma : Matrix I I ℂ)
    (hrho : IsDensityMatrix rho) (hgamma : IsDensityMatrix gamma) :
    (∑ v, |subspaceProbability rho (O.proj v) -
      subspaceProbability gamma (O.proj v)|) ≤ traceNorm (rho - gamma) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
