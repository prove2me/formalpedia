-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_postAmplification
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.postAmplification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:37:27.555891+00:00
-- url     : https://prove2.me/theorems/c157e040-cc42-43f1-a8bb-751c26447281
-- title:
--   Corollary 5, Eqs.(9)–(10): post-amplification converts loss to displacement
-- statement:
--   Let $0<\eta\le1$ and $b\ge0$. Write $\mathcal N[\eta,b]$ for thermal loss with environmental mean photon number $b$, $\mathcal A[G]$ for the quantum-limited amplifier of intensity gain $G$, and $\mathcal B_s$ for Gaussian random displacement of quadrature variance $s$. Then, on every trace-class input,
--
--   $$\mathcal A[1/\eta]\circ\mathcal N[\eta,b]=\mathcal B_{(1-\eta)(b+1)/\eta}.$$
--
--   All maps are actual normal CPTP maps on the full Fock space. At $\eta=1$, the zero-noise displacement channel is the identity. This identifies the noise incurred by post-amplification.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 3, Corollary 5, Eqs.(9)–(10): post-amplification converts loss to displacement

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Corollary 5, PDF p.3 Eqs.(9)--(10). Printed eta=0 is excluded because
1/eta is not a finite amplifier gain; eta=1 uses the identity noise endpoint. -/
theorem postAmplification (eta b : ℝ) (h0 : 0 < eta) (h1 : eta ≤ 1) (hb : 0 ≤ b) :
    C.IsNormalFockChannel (C.thermal eta b) ∧
    C.IsNormalFockChannel (C.amplifier (1 / eta)) ∧
    C.IsNormalFockChannel (C.displacementNoiseChannel ((1 - eta) / eta * (b + 1))) ∧
    B.AmplifierRealized (Real.sqrt (1 / eta)) ∧ B.DisplacementRealized ∧
    ∀ X, B.IsTraceClass X →
      C.amplifier (1 / eta) (C.thermal eta b X) =
        C.displacementNoiseChannel ((1 - eta) / eta * (b + 1)) X := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
