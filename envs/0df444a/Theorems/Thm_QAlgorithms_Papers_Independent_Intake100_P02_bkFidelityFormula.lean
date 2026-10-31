-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P02_bkFidelityFormula
-- name    : QAlgorithms.Papers.Independent.Intake100.P02.bkFidelityFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:51:38.67384+00:00
-- url     : https://prove2.me/theorems/e38843ce-4f8d-4375-bddb-c3b49eedc850
-- title:
--   Explicit BK/TMSV root fidelity
-- statement:
--   Use $[q,p]=i$ and vacuum covariance $I/2$. Let $\mu,t\ge1/2$ be finite resource and input TMSV variances, respectively, and set $\xi(\mu)=2\mu-\sqrt{4\mu^2-1}$. Let $\Phi_t$ be the normalized TMSV density with Schmidt amplitudes $v_j=\sqrt{(t-1/2)^j/(t+1/2)^{j+1}}$. Independently construct $Y_{\mu,t}$ by applying the random displacement $D(z)$ only to the transmitted mode of $\Phi_t$, averaging over the isotropic complex Gaussian law of variance $\xi(\mu)$ and retaining the reference mode. The construction is normalized; its coefficient integrals and pure-input overlap series converge. The unsquared fidelity is $F(\mu,t)=\sqrt{\langle\Phi_t|Y_{\mu,t}|\Phi_t\rangle}$, and
--
--   $$F(\mu,t)=\frac{1}{\sqrt[4]{1-4t\bigl[\sqrt{4\mu^2-1}+t-2\mu(1+2t\xi(\mu))\bigr]}}.$$
--
--   This identifies the fidelity of actual full Fock-space states, rather than defining it by the closed formula. Both vacuum endpoints are included.
-- source:
--   Theory of channel simulation and bounds for private communication, arXiv:1711.09909v3, PDF p. 28, Appendix A, Eq. (A4): explicit BK/TMSV root fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P02

open Filter MeasureTheory QAlgorithms

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal)

/-- arXiv:1711.09909v3, PDF p.28, Appendix A, (A4): explicit root fidelity.
The whole bracket is inside the fourth root sqrt(sqrt(.)); vacuum endpoints
mu=t=1/2 are allowed. Well-definedness guards are conclusions. -/
theorem bkFidelityFormula (mu t : ℝ) (hmu : 1 / 2 ≤ mu) (ht : 1 / 2 ≤ t) :
    IsDensity (tmsvKernel t) ∧ IsDensity (bkOutput mu t) ∧
    IsProbabilityMeasure (complexNormal (bkNoise mu) 0) ∧
    (∀ x y : ℕ × ℕ, Integrable (fun z : ℂ => displacedTmsvKernel t z x y)
      (complexNormal (bkNoise mu) 0)) ∧
    Summable (bkOverlapTerm mu t) ∧
    bkRootFidelity mu t =
      1 / Real.sqrt (Real.sqrt
        (1 - 4 * t * (Real.sqrt (4 * mu ^ 2 - 1) + t -
          2 * mu * (1 + 2 * t * bkNoise mu)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P02

end
