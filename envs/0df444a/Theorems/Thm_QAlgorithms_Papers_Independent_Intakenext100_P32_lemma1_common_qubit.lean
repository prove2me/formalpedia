-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P32_lemma1_common_qubit
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P32.lemma1_common_qubit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:00:52.442+00:00
-- url     : https://prove2.me/theorems/15766761-55e6-4cb8-98bc-fb4db4a7f79d
-- title:
--   Common-qubit trace-distance and root-fidelity inequality
-- statement:
--   Let $\rho$ and $\sigma$ be positive trace-class operators of trace one on a complex Hilbert space $H$. Suppose both supports are contained in one common subspace of complex dimension at most two. Write $D(\rho,\sigma)=\tfrac12\operatorname{Tr}|\rho-\sigma|$ and $F(\rho,\sigma)=\operatorname{Tr}|\sqrt\rho\sqrt\sigma|$ for trace distance and unsquared root fidelity. Then
--
--   $$1-F(\rho,\sigma)^2\le D(\rho,\sigma).$$
--
--   This strengthens the general trace-distance lower bound for a common qubit support. Pure and coincident states are included, as are states with a zero Bloch vector.
-- source:
--   Degrees of concealment and bindingness in quantum bit commitment protocols, arXiv:quant-ph/0106019v2, PDF p. 4, Lemma 1; appendix pp.10–11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P32

open QAlgorithms.Papers.Independent.Support50.P44
  (IsHilbertDensity hilbertFidelity hilbertTraceNorm)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.4, Lemma 1; proof in the appendix, PDF pp.10--11.
Fidelity is unsquared root fidelity; trace distance is HALF the trace norm.
Pure states, coincident states and zero Bloch vectors are included. -/
theorem lemma1_common_qubit
    {I : Type*} (basis : HilbertBasis I ℂ H) (rho sigma : H →L[ℂ] H)
    (hrho : IsHilbertDensity basis rho) (hsigma : IsHilbertDensity basis sigma)
    (hsupport : CommonQubitSupport rho sigma) :
    1 - hilbertFidelity basis rho sigma ^ 2 ≤
      hilbertTraceNorm basis (rho - sigma) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P32

end
