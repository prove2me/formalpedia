-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P02_amplifiedSplitting
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P02.amplifiedSplitting
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:49:26.177992+00:00
-- url     : https://prove2.me/theorems/96887312-dc85-4c5b-86e5-97fc68c9048d
-- title:
--   Reflected-mode leakage and positive gain for splitting plus amplification
-- statement:
--   Let $n>0$, $0<\eta\le1$ and finite intensity gain $g\ge1$ be given. Eve splits each coherent pulse, retaining fraction $1-\mu$, and applies a quantum-limited phase-insensitive amplifier to Bob's fraction $\mu$. Only the reflected mode is assigned to Eve. With $v=1/4$, the matching observed parameters satisfy
--   $$
--   v_{\mathrm{obs}}=(2g-1)v,\qquad
--   \mu=\frac\eta g=\frac{2v\eta}{v_{\mathrm{obs}}+v},\qquad
--   g\mu n=\eta n.
--   $$
--   Here $0<\mu\le1$ and $(1-\mu)n\ge(1-\eta)n$. For every coherent input $\alpha$, the joint output is the normalized product of Bob's Gaussian mixture, with mean amplitude $\sqrt\eta\alpha$ and total complex displacement variance $g-1$, and Eve's reflected coherent state $|\sqrt{1-\mu}\alpha\rangle$. Bob's quadrature law is Gaussian with variance $v_{\mathrm{obs}}$ and finite second moment.
--
--   After the basis announcement, Eve's optimized reflected-mode information and the corresponding ideal-correction gain obey
--   $$
--   I_L^R(n,\eta,g)=I^R_{\mathrm{opt}}(n,\eta/g)
--   =\log_2\!\left(2-e^{-(1-\eta/g)n/v}\right),\qquad 0\le I_L^R<1.
--   $$
--   There is a finite $t\ge0$ with $i_{AB}(t;\eta n,v_{\mathrm{obs}})\ge I_L^R$ such that the per-emitted-pulse gain is strictly positive at every finite threshold $x_0\ge t$.
--
--   This explicit compatible attack supplies a lower bound on worst-case leakage. Positive gain against this attack is not a guarantee against all Gaussian attacks. The source's strict lower bound on leakage is corrected to a non-strict one at $\eta=g=1$; equality of the two reflected intensities is allowed at $g=1$.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, PDF p. 3, Eqs.(11)–(12) and following paragraph

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

/-- PDF p.3, (11)–(12) and following paragraph: the explicit splitting plus
amplification attack supplies the stated reflected-mode leakage and positive
gain. Printed 0<I_L is corrected to 0<=I_L at eta=g=1; printed 'more intense'
is non-strict at g=1. Both corrections preserve the source's positive-gain result.
An attack compatible with these observations gives a lower bound on the worst
possible leakage, never a security guarantee against every Gaussian attack. -/
theorem amplifiedSplitting (n eta g : ℝ) (hn : 0 < n) (heta : 0 < eta)
    (hetaOne : eta ≤ 1) (hg : 1 ≤ g) :
    (0 < eta / g ∧ eta / g ≤ 1) ∧
    g * (eta / g) * n = eta * n ∧
    eta / g = 2 * (1 / 4 : ℝ) * eta / (amplifiedVariance g + (1 / 4 : ℝ)) ∧
    (1 - eta) * n ≤ (1 - eta / g) * n ∧
    (∀ alpha : ℂ, IsDensity (splittingAmplifierOutput eta g alpha) ∧
      MixtureIntegrable ((Real.sqrt eta : ℂ) * alpha) (g - 1) ∧
      ∀ k : Bool,
        displacedHomodyne ((Real.sqrt eta : ℂ) * alpha) (g - 1) k =
          gaussianReal (coherentAmplitudeQuadrature k ((Real.sqrt eta : ℂ) * alpha))
            ⟨amplifiedVariance g, by
              dsimp [amplifiedVariance]
              nlinarith⟩ ∧
        MemLp (fun x : ℝ => x) 2
          (displacedHomodyne ((Real.sqrt eta : ℂ) * alpha) (g - 1) k) ∧
        variance (fun x : ℝ => x)
          (displacedHomodyne ((Real.sqrt eta : ℂ) * alpha) (g - 1) k) =
            amplifiedVariance g) ∧
    amplifiedLeakage n eta g =
      Real.logb 2 (2 - Real.exp (-((1 - eta / g) * n) / (1 / 4 : ℝ))) ∧
    (0 ≤ amplifiedLeakage n eta g ∧ amplifiedLeakage n eta g < 1) ∧
    (∃ t : ℝ, 0 ≤ t ∧
      amplifiedLeakage n eta g ≤ homodyneInformation (amplifiedVariance g) (eta * n) t ∧
      ∀ x0 : ℝ, t ≤ x0 → 0 < amplifiedGain x0 n eta g) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P02

end
