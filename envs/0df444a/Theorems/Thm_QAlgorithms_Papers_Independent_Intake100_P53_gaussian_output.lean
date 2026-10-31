-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_gaussian_output
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.gaussian_output
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:44:20.965914+00:00
-- url     : https://prove2.me/theorems/c0a92e14-12c2-4599-9a0b-6953b37a832b
-- title:
--   §IV, (4)–(5): heterodyne law of displaced thermal output
-- statement:
--   Let $\kappa>0$, $0<\eta\le1$, and $\delta\ge0$ be finite real parameters. Alice modulates normalized oscillator coherent states with density $\exp(-|\alpha|^2/(2\kappa))/(2\pi\kappa)$ relative to planar Lebesgue measure. Bob's tomographically verified output is $D(\sqrt\eta\alpha)\tau_{\delta/2}D(\sqrt\eta\alpha)^\dagger$, where $\tau_n$ is the thermal state of mean photon number $n$, and he uses ideal heterodyne detection. Bits are the signs of the real parts, with bit zero for a nonnegative real part. Public announcements are $a=(u,y)=(|\Re\alpha|,\Im\alpha)$ and $b=(w,z)=(|\Re\beta|,\Im\beta)$. Zero-real-part events have probability zero. All formulas below concern the source's collective-attack, infinite-key setting with completed tomography; they assert no finite-sample or coherent-attack security.
--
--   The actual thermal, coherent, and displacement coefficient constructors realize their intended oscillator objects, and $\rho_B^\alpha$ is a normalized positive trace-class density. Its heterodyne density is
--
--   $$\frac{\langle\beta|\rho_B^\alpha|\beta\rangle}{\pi}=p(\beta\mid\alpha)=\frac{2}{\pi(2+\delta)}\exp\!\left(-\frac{2|\beta-\sqrt\eta\alpha|^2}{2+\delta}\right).$$
--
--   For every $\alpha$, this density is integrable and integrates to one. Both real and imaginary coordinate second moments around $\sqrt\eta\alpha$ are genuine integrals equal to $(2+\delta)/4$. Consequently the vacuum heterodyne variance is $1/2$, and the convention $\delta=2(\operatorname{Var}_{\rm obs}/\operatorname{Var}_{\rm vac}-1)$ is retained. The zero-noise endpoint yields the coherent-state Husimi law.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 3, §IV, (4)–(5): heterodyne law of displaced thermal output

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.3, IV, (4)--(5): displaced-thermal heterodyne law. Realization and
density conclusions exclude the accepted constructors' fallback values.
The zero-noise and identity-channel endpoints are included. -/
theorem gaussian_output (P : CoherentHeterodyneParameters) :
    CoherentRealized ∧ ThermalRealized (1 + P.delta) ∧
    ∀ alpha : ℂ,
      HasFockMatrix (displacement ((Real.sqrt P.eta : ℂ) * alpha))
        (displacementMatrix ((Real.sqrt P.eta : ℂ) * alpha)) ∧
      IsDensity (receivedState P alpha) ∧
      (∀ beta : ℂ, husimiQ (receivedState P alpha) beta / Real.pi = heterodyneDensity P alpha beta) ∧
      Integrable (heterodyneDensity P alpha) volume ∧
      (∫ beta : ℂ, heterodyneDensity P alpha beta) = 1 ∧
      (∀ coordinate : Bool,
        let center := if coordinate then Real.sqrt P.eta * alpha.im else Real.sqrt P.eta * alpha.re
        Integrable (fun beta : ℂ =>
          ((if coordinate then beta.im else beta.re) - center) ^ 2 * heterodyneDensity P alpha beta) volume ∧
        (∫ beta : ℂ,
          ((if coordinate then beta.im else beta.re) - center) ^ 2 * heterodyneDensity P alpha beta) =
          (2 + P.delta) / 4) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
