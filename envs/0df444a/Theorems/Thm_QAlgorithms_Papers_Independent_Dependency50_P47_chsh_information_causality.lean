-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_chsh_information_causality
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.chsh_information_causality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:48:37.013466+00:00
-- url     : https://prove2.me/theorems/71854432-59b2-4112-a117-a2f8b89f3320
-- title:
--   Appendix C unnumbered: Information Causality lower bound on quantum simulation cost
-- statement:
--   For binary variables with uniform independent inputs, let the CHSH conditional law have bias $0\le\beta\le1$: a winning output pair has probability $(1+\beta)/4$ and a losing pair $(1-\beta)/4$. Let $h$ be binary entropy in bits. For every positive integer $n$ and every achievable entanglement-assisted one-way simulation rate $R$,
--
--   $$
--   R\ge\frac{2^n}{2^n-1}\left(1-h\!\left(\frac{1+\beta^n}{2}\right)\right)-\frac1{2^n-1}.
--   $$
--
--   The exponent parameter is separate from the blocklength in the definition of an achievable rate. The restriction $n\ge1$ keeps the denominator positive. This is the paper's quantum application of Information Causality, not an assertion about unspecified physical theories.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 25, Appendix C unnumbered: Information Causality lower bound on quantum simulation cost

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Appendix C, PDF p.25: Information Causality lower bound; n=0 is excluded because
2^n-1 would vanish. All rates in the achievable quantum region satisfy the bound. -/
theorem chsh_information_causality (bias : ℝ) (h0 : 0 ≤ bias) (h1 : bias ≤ 1)
    (p : Law (Fin 2 × Fin 2 × Fin 2 × Fin 2)) (hp : IsCHSHLaw bias p) (n : ℕ) (hn : 0 < n) :
    ∀ R ∈ quantumRates p,
      (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1) * (1 - binEntropy2 ((1 + bias ^ n) / 2)) -
        1 / ((2 : ℝ) ^ n - 1) ≤ R := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
