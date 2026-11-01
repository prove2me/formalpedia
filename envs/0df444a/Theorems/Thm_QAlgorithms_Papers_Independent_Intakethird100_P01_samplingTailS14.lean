-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P01_samplingTailS14
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P01.samplingTailS14
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:44:32.996326+00:00
-- url     : https://prove2.me/theorems/c7d092e6-d170-484a-baac-643011483b96
-- title:
--   Finite-population tail probability conditioned on passing parameter estimation
-- statement:
--   Let $n,k$ be positive integers and $N=n+k$. Let $(Z_{\mathrm{tot}},Z'_{\mathrm{tot}})$ have any normalized joint probability distribution on two $N$-bit strings. Independently of these strings, draw a uniformly random $k$-element subset $T$ of the positions. Let $\Lambda$ be the relative Hamming distance on $T$ and let $\Lambda_{\mathrm{key}}$ be the relative Hamming distance on its complement. Fix $0\le Q_{\mathrm{tol}}\le1$, define the event $\mathrm{pass}=\{\Lambda\le Q_{\mathrm{tol}}\}$, and assume $p_{\mathrm{pass}}=\Pr[\mathrm{pass}]>0$. For any $\mu\ge0$, put
--   $$
--   \varepsilon=\exp\!\left(-\frac{kn}{N}\frac{k}{k+1}\mu^2\right).
--   $$
--   Then
--   $$
--   \Pr[\Lambda_{\mathrm{key}}\ge\Lambda+\mu\mid\mathrm{pass}]
--   \le\frac{\varepsilon^2}{p_{\mathrm{pass}}}.
--   $$
--   This is a sampling-without-replacement estimate for arbitrary correlated strings. Applying it to an interactive QKD execution requires separately deriving the stated independent uniform sampling experiment.
-- source:
--   Tight Finite-Key Analysis for Quantum Cryptography, arXiv:1103.4130v2, PDF p. 13, Supplementary Note 2, Eqs. (S11)–(S14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P01

namespace QAlgorithms.Papers.Independent.Intakethird100.P01

open scoped BigOperators ComplexConjugate ComplexOrder

-- Accepted extended entropy: the finite-real smoothing helper excludes radius >= 1.

open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized purifiedDistance conditionalMaxEntropy smoothConditionalMaxEntropyExtended)

noncomputable section

/-- PDF p.13, Eqs.(S11)--(S14): the pass-conditioned finite-population tail bound.
The sample is drawn independently of an arbitrary normalized joint law of the total strings. -/
theorem samplingTailS14 (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (P : StringPair (n + k) → ℝ) (hP : ∀ z, 0 ≤ P z) (hPsum : ∑ z, P z = 1)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hpass : 0 < passProbability P Q)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    probabilityGivenPass P Q (fun w => complementErrorFraction w ≥ sampleError w + mu) ≤
      (samplingFailureParameter n k mu) ^ 2 / passProbability P Q := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P01
