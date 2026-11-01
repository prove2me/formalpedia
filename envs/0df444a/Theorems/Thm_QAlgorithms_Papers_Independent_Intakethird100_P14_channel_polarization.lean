-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_channel_polarization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.channel_polarization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:54:59.85742+00:00
-- url     : https://prove2.me/theorems/d68053ce-e27d-4650-b663-37796a36dab5
-- title:
--   Both limiting fractions of polarized split channels
-- statement:
--   Let $W$ be any binary-input classical–quantum channel with normalized density outputs on a common complex Hilbert space. Its information $I(W)$ uses a uniform binary input and base-two logarithms. For $N=2^n$, let $W_N^{(i)}$ be the actual split channels obtained by encoding with $G_N$, exposing the previous bits as a classical register, and averaging the later bits uniformly. For every real $\delta\in(0,1)$,
--
--   $$\frac{\bigl|\{i:I(W_N^{(i)})\in(1-\delta,1]\}\bigr|}{N}\longrightarrow I(W),\qquad
--   \frac{\bigl|\{i:I(W_N^{(i)})\in[0,\delta)\}\bigr|}{N}\longrightarrow1-I(W).$$
--
--   Both limits are taken as $n\to\infty$. No symmetry, purity, finite-dimensionality, or strict inequality $0<I(W)<1$ is assumed. These fractions quantify the information carried by the polarized good and bad channels.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 4, Theorem 2 (Channel Polarization)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2, PDF p.4; proof p.8. Both endpoint fractions, with exactly the
source's open and closed interval endpoints, converge along N=2^n. -/
theorem channel_polarization {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun n =>
      ((Finset.univ.filter (fun i : PolarWire n =>
        ENNReal.ofReal (1 - delta) < symmetricInformation (splitChannel W n i) ∧
        symmetricInformation (splitChannel W n i) ≤ 1)).card : ℝ≥0∞) / (2 ^ n : ℕ))
      atTop (nhds (symmetricInformation W)) ∧
    Tendsto (fun n =>
      ((Finset.univ.filter (fun i : PolarWire n =>
        0 ≤ symmetricInformation (splitChannel W n i) ∧
        symmetricInformation (splitChannel W n i) < ENNReal.ofReal delta)).card : ℝ≥0∞) /
          (2 ^ n : ℕ)) atTop (nhds (1 - symmetricInformation W)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
