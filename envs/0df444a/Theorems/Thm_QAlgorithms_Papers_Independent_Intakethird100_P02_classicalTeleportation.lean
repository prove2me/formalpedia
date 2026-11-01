-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P02_classicalTeleportation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P02.classicalTeleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:49:58.4977+00:00
-- url     : https://prove2.me/theorems/335d7333-ca8c-4750-b940-1e72668b8689
-- title:
--   Classical teleportation, reduced excess noise, and no information advantage
-- statement:
--   In classical teleportation (CT), the rescaled simultaneous-quadrature measurement result $z$ for coherent input $\alpha$ has density $e^{-|z-\alpha|^2}/\pi$. Eve retains $z$ and resends the coherent state $|z\rangle$. After optional vacuum loss of intensity $0<\eta\le1$, the measure–prepare output equals
--   $$
--   \rho_{\mathrm{CT},\eta}(\alpha)=\frac1{\pi\eta}\int_{\mathbb C}e^{-|\beta|^2/\eta}
--   |\sqrt\eta\alpha+\beta\rangle\langle\sqrt\eta\alpha+\beta|\,d^2\beta.
--   $$
--   All matrix coefficient integrals exist, and the output is a positive trace-class operator of trace one. Each quadrature has a Gaussian law of mean $\sqrt\eta$ times the input quadrature, finite second moment, and variance
--   $$
--   v_{\mathrm{obs}}=(1+2\eta)v,\qquad v=1/4,\qquad \delta=v_{\mathrm{obs}}/v-1=2\eta.
--   $$
--   In particular, at $\eta=1$ this is Eq.(13), with variance $3v$.
--
--   For any probability ensemble of classical symbols $A$ and measurable amplitude encoding, generate Eve's result $Z$ by this simultaneous measurement. Let Bob's record $B$ have any normalized measurable conditional law depending only on the resent amplitude $\sqrt\eta Z$. Then the classical Shannon mutual information, defined by relative entropy and measured in bits with infinity allowed, obeys
--   $$
--   I(A;B)\le I(A;Z).
--   $$
--   This states the source's absence of information advantage. Its printed strict inequality is corrected to a non-strict inequality, since a one-symbol ensemble gives equality. The separate universal public-discussion security converse is deferred.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, PDF p. 4, Eqs.(13)–(14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P02

open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator coherentKet coherentCoefficient)

open QAlgorithms.Papers.Independent.Frontier30.P21 (coherentDensity)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal quadrature)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity productCoeff)

/-- PDF pp.3–4, (13)–(14): actual intercept–resend mixture, the reduced
quadrature excess after vacuum loss, and no information advantage. The printed
strict I_AB<I_E is corrected to <=, since deterministic Alice symbols or a
constant receiver give equality. This is a data-processing statement; the
universal operational public-discussion converse is separately deferred. -/
theorem classicalTeleportation (eta : ℝ) (heta : 0 < eta) (hetaOne : eta ≤ 1) :
    (∀ (alpha : ℂ) (k : Bool),
      (∀ j l, Integrable
        (fun z : ℂ => coherentDensity ((Real.sqrt eta : ℂ) * z) j l)
          (complexNormal 1 alpha)) ∧
      classicalTeleportationOutput eta alpha =
        displacedCoherent ((Real.sqrt eta : ℂ) * alpha) eta ∧
      IsDensity (classicalTeleportationOutput eta alpha) ∧
      classicalTeleportationHomodyne eta alpha k =
        gaussianReal (Real.sqrt eta * coherentAmplitudeQuadrature k alpha)
          ⟨(1 + 2 * eta) * (1 / 4 : ℝ), by
              positivity⟩ ∧
      MemLp (fun x : ℝ => x) 2 (classicalTeleportationHomodyne eta alpha k) ∧
      variance (fun x : ℝ => x) (classicalTeleportationHomodyne eta alpha k) =
        (1 + 2 * eta) * (1 / 4 : ℝ)) ∧
    normalizedExcess ((1 + 2 * eta) * (1 / 4 : ℝ)) = 2 * eta ∧
    (∀ (A O : Type) [MeasurableSpace A] [MeasurableSpace O]
      (mu : Measure A) [IsProbabilityMeasure mu]
      (amplitude : A → ℂ), Measurable amplitude →
      ∀ (receiver : Kernel ℂ O) [IsMarkovKernel receiver],
        mutualInformationBits (aliceBobLaw mu amplitude eta receiver) ≤
          mutualInformationBits (aliceEveLaw mu amplitude)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P02

end
