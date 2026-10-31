-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_ideal_sifting_variants
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.ideal_sifting_variants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:38:39.912185+00:00
-- url     : https://prove2.me/theorems/fac79935-c767-4345-bd49-338f7799d695
-- title:
--   Ideal sifting coefficients for COW pairing and announcement variants
-- statement:
--   In Appendix A’s no-Eve, no-dark-count, long-distance model with mean nonempty intensity $\mu\ge0$ and balanced pulse occupancy, ideal sifted bits are uniform and perfectly correlated. Hence their mutual information is one bit. Original COW with negligible decoys, COWm1 with negligible unused pulses, and COWm2 with valid Alice-defined pairs have coefficient $\mu/2$ per $t\eta$. For a completely random balanced train paired consecutively a posteriori, mixed pairs occur with probability one half; Bob’s specified pairing model has the same acceptance fraction. Thus
--
--   $$r_s/(t\eta)=\mu/2\quad\text{for valid Alice-defined pairs},\qquad r_s/(t\eta)=\mu/4\quad\text{for the random/Bob variants}.$$
--
--   For on/off click announcements, let $q$ be the nonempty fraction, $x$ the first-order nonempty click probability, and $0\le f_0\le1-qx$ the unconditional additional selected nonclick fraction. Assuming $qx<1$, keep every click and select a fraction $f_0/(1-qx)$ of nonclick slots. The resulting sifted mass is $qx+f_0$. These are ideal information/sifting calculations, not security guarantees or an optimization of practical error correction.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 11, Appendix A, unnumbered: ideal sifting rates of COW variants

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- Appendix A pp.11–12: ideal sifting coefficients (times t eta) of the five
pairing variants, with one bit per sifted detection. Longer dit encodings and
practical error-correction optimization are proposals, outside this result. -/
theorem ideal_sifting_variants (mu : ℝ) (hmu : 0 ≤ mu) :
    QAlgorithms.mutualInfoBits idealBitLaw = 1 ∧
    idealSiftingCoefficient 0 mu = mu/2 ∧
    idealSiftingCoefficient 1 mu = mu/2 ∧
    idealSiftingCoefficient 2 mu = mu/2 ∧
    idealSiftingCoefficient 3 mu = mu/4 ∧
    idealSiftingCoefficient 4 mu = mu/4 ∧
    (∀ (q x f0 : ℝ), q ∈ Set.Icc (0:ℝ) 1 → x ∈ Set.Icc (0:ℝ) 1 →
      q*x < 1 → f0 ∈ Set.Icc (0:ℝ) (1-q*x) →
      (∑ ab, announcedLaw q x f0 ab) = q*x+f0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
