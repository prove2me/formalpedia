-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P02_postselection_positiveGain
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P02.postselection_positiveGain
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:47:56.421207+00:00
-- url     : https://prove2.me/theorems/826dbe3c-83d4-459e-bde7-9900194446e1
-- title:
--   Positive gain at sufficiently large finite postselection thresholds
-- statement:
--   Fix any emitted intensity $n>0$ and transmissivity $0<\eta\le1$ in the four-state protocol, with coherent quadrature variance $v=1/4$, basis-match probability $1/2$ and ideal error correction. Eve measures individual reflected pulses after learning the basis. Let $I^R_{\mathrm{opt}}(n,\eta)$ denote her optimized collision/Rényi information, let $i_{AB}(x)$ be Bob's conditional Shannon information for received intensity $\eta n$, and let $G$ be the unconditioned per-emitted-pulse gain of Eq.(8). Then $0\le I^R_{\mathrm{opt}}<1$, and there is a finite $t\ge0$ such that
--   $$
--   i_{AB}(t)\ge I^R_{\mathrm{opt}}(n,\eta),\qquad
--   G(x_0,n,\eta)>0\quad\text{for every finite }x_0\ge t.
--   $$
--   Moreover, every nonnegative $t$ satisfying the displayed information inequality has this positive-gain property.
--
--   Thus at each fixed positive intensity the individual splitting attack imposes no loss limit when postselection is available. The result includes $\eta=1$ and does not include $\eta=0$ or infinite thresholds.
-- source:
--   A practical limitation for continuous-variable quantum cryptography using coherent states, arXiv:quant-ph/0403115v1, PDF p. 2, Eq.(9) and PDF p.3 first paragraph

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

/-- PDF pp.2–3, (9) and following paragraph: at every fixed positive emitted
intensity and nonzero transmissivity there is a finite threshold with positive
gain, and every nonnegative threshold satisfying (9) has a strictly positive
tail gain. This is restricted to individual splitting attacks. -/
theorem postselection_positiveGain (n eta : ℝ) (hn : 0 < n)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) :
    (0 ≤ optimalLeakage n eta ∧ optimalLeakage n eta < 1) ∧
    (∃ t : ℝ, 0 ≤ t ∧
      optimalLeakage n eta ≤ homodyneInformation (1 / 4 : ℝ) (eta * n) t ∧
      ∀ x0 : ℝ, t ≤ x0 → 0 < splittingGain x0 n eta) ∧
    (∀ t : ℝ, 0 ≤ t →
      optimalLeakage n eta ≤ homodyneInformation (1 / 4 : ℝ) (eta * n) t →
      ∀ x0 : ℝ, t ≤ x0 → 0 < splittingGain x0 n eta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P02

end
