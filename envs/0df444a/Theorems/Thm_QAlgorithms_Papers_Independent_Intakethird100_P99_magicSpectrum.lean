-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_magicSpectrum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.magicSpectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:17:27.191682+00:00
-- url     : https://prove2.me/theorems/d8c493a9-2e4e-4a58-91d0-c45d2845b9d9
-- title:
--   Magic-basis spectrum determines the interaction phases modulo pi
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. Fix an actual phase-compatible decomposition $U=(A\otimes B)U_\beta(C\otimes D)$ with $A,B,C,D\in\mathrm{SU}(2)$. Let $M$ be the matrix of this chosen representative in the ordered magic basis $-i(|01\rangle+|10\rangle)/\sqrt2$, $(|00\rangle+|11\rangle)/\sqrt2$, $-i(|00\rangle-|11\rangle)/\sqrt2$, $(|01\rangle-|10\rangle)/\sqrt2$. Put $\lambda=(\beta_1+\beta_2-\beta_3,\beta_1-\beta_2+\beta_3,-\beta_1+\beta_2+\beta_3,-\beta_1-\beta_2-\beta_3)$. Then, for polynomial indeterminate $x$,
--
--   $$\operatorname{charpoly}(M^{T}M)(x)=\prod_{j=1}^{4}\bigl(x-e^{-2i\lambda_j}\bigr).$$
--
--   Transpose here has no complex conjugation. Multiplicities are retained; phases determine the $\lambda_j$ modulo $\pi$, and principal arguments alone need not select the canonical chamber.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 13, Appendix A: spectrum determines interaction phases

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.13, Appendix A: the characteristic polynomial counts all four eigenphases
with multiplicity, for a phase-compatible decomposition. No principal-argument uniqueness
is asserted. The appendix's printed H=exp(sum ...) is corrected to H=sum ... as in (3). -/
theorem magicSpectrum (U : TwoMatrix) (b : Triple)
    (hU : PhaseCompatibleContent U b) :
    ((magicMatrix U).transpose * magicMatrix U).charpoly =
      ∏ j : Fin 4, (Polynomial.X - Polynomial.C
        (Complex.exp (-2 * Complex.I * (interactionPhases b j : ℂ)))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
