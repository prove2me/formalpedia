-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P32_lemma2_maximum_squared_fidelities
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P32.lemma2_maximum_squared_fidelities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:01:36.416991+00:00
-- url     : https://prove2.me/theorems/97c11835-7ae0-41b7-a1f0-abad14236cad
-- title:
--   Attained maximum of the sum of two squared root fidelities
-- statement:
--   Let $\sigma$ and $\omega$ be positive trace-class operators of trace one on a complex Hilbert space $H$, and let $F$ denote unsquared root fidelity. Maximizing over all positive trace-class operators $\rho$ of trace one on that same space gives
--
--   $$\max_{\rho}\bigl(F(\rho,\sigma)^2+F(\rho,\omega)^2\bigr)=1+F(\sigma,\omega).$$
--
--   The maximum is attained: there exists a density operator with the displayed value, and every density operator has value at most that quantity. This identity is the state-space optimization used to analyze Alice's control.
-- source:
--   Degrees of concealment and bindingness in quantum bit commitment protocols, arXiv:quant-ph/0106019v2, PDF p. 4, Lemma 2; derivation p.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P32

open QAlgorithms.Papers.Independent.Support50.P44
  (IsHilbertDensity hilbertFidelity hilbertTraceNorm)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.4, Lemma 2; the maximization is derived on PDF p.7.
An actual maximizing density operator is asserted, together with the upper bound
for EVERY density operator. The right side contains root fidelity WITHOUT a square. -/
theorem lemma2_maximum_squared_fidelities
    {I : Type*} (basis : HilbertBasis I ℂ H) (sigma omega : H →L[ℂ] H)
    (hsigma : IsHilbertDensity basis sigma) (homega : IsHilbertDensity basis omega) :
    ∃ rho : H →L[ℂ] H, IsHilbertDensity basis rho ∧
      hilbertFidelity basis rho sigma ^ 2 + hilbertFidelity basis rho omega ^ 2 =
        1 + hilbertFidelity basis sigma omega ∧
      ∀ tau : H →L[ℂ] H, IsHilbertDensity basis tau →
        hilbertFidelity basis tau sigma ^ 2 + hilbertFidelity basis tau omega ^ 2 ≤
          1 + hilbertFidelity basis sigma omega := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P32

end
