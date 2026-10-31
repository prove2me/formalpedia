-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P32_qutrit_linear_saturation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P32.qutrit_linear_saturation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:02:29.476951+00:00
-- url     : https://prove2.me/theorems/cb44a6f9-3029-47b0-a38b-4e47422673c5
-- title:
--   Qutrit saturation of D+F=1 and necessity of dimension three in the interior
-- statement:
--   For $0\le\lambda\le1$, define density matrices on $\mathbb C^3$ by $\rho_0(\lambda)=\operatorname{diag}(\lambda,1-\lambda,0)$ and $\rho_1(\lambda)=\operatorname{diag}(0,1-\lambda,\lambda)$. Their trace distance $D=\tfrac12\operatorname{Tr}|\rho_0-\rho_1|$ and unsquared root fidelity $F=\operatorname{Tr}|\sqrt{\rho_0}\sqrt{\rho_1}|$ satisfy
--
--   $$D(\rho_0(\lambda),\rho_1(\lambda))=\lambda,\qquad F(\rho_0(\lambda),\rho_1(\lambda))=1-\lambda,\qquad D+F=1.$$
--
--   For any density operators on any complex Hilbert space satisfying $D+F=1$ and $0<F<1$, their two supports cannot be contained in a common subspace of dimension at most two. Together these assertions show that dimension three is the smallest possible common ambient dimension for interior saturation.
--
--   The family includes both endpoints. The interior qualification corrects the printed dimension claim: identical states and orthogonal pure states already saturate at the endpoints. This correction requires independent moderation.
-- source:
--   Degrees of concealment and bindingness in quantum bit commitment protocols, arXiv:quant-ph/0106019v2, PDF p. 8, §VI.B, first explicit family

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P32

open QAlgorithms.Papers.Independent.Support50.P44
  (IsHilbertDensity hilbertFidelity hilbertTraceNorm)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.8, Section VI.B: the qutrit family has D=lam and F=1-lam,
including both endpoints. Source correction: the printed claim that dimension
three is necessary requires INTERIOR saturation, 0<F<1; identical states and
orthogonal pure states are endpoint counterexamples. The second clause excludes
common support of dimension at most two for every interior saturating pair,
on arbitrary Hilbert spaces. Independent moderation of this correction is pending. -/
theorem qutrit_linear_saturation
    {I : Type*} (basis : HilbertBasis I ℂ H) :
    (∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      IsDensityMatrix (qutritToken false lam) ∧
      IsDensityMatrix (qutritToken true lam) ∧
      traceNorm (qutritToken false lam - qutritToken true lam) / 2 = lam ∧
      rootFidelity (qutritToken false lam) (qutritToken true lam) = 1 - lam ∧
      traceNorm (qutritToken false lam - qutritToken true lam) / 2 +
        rootFidelity (qutritToken false lam) (qutritToken true lam) = 1) ∧
    (∀ rho sigma : H →L[ℂ] H,
      IsHilbertDensity basis rho → IsHilbertDensity basis sigma →
      hilbertTraceNorm basis (rho - sigma) / 2 + hilbertFidelity basis rho sigma = 1 →
      0 < hilbertFidelity basis rho sigma → hilbertFidelity basis rho sigma < 1 →
      ¬ CommonQubitSupport rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P32

end
