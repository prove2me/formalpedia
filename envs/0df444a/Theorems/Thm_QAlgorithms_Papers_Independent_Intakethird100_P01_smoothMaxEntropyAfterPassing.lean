-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P01_smoothMaxEntropyAfterPassing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P01.smoothMaxEntropyAfterPassing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:45:20.830142+00:00
-- url     : https://prove2.me/theorems/2576973a-2089-4a1f-bfc7-c7818ebc8d7f
-- title:
--   Lemma 3: smooth max-entropy of the pass-conditioned key pair
-- statement:
--   Let $n,k$ be positive integers and $N=n+k$. Give two $N$-bit strings an arbitrary normalized joint law. Independently choose a uniform $k$-subset of positions for testing and retain the complementary $n$ positions in their original order. Let $\Lambda$ denote the test relative Hamming distance. For $0\le Q_{\mathrm{tol}}\le1$, condition on $\mathrm{pass}=\{\Lambda\le Q_{\mathrm{tol}}\}$ and assume $p_{\mathrm{pass}}=\Pr[\mathrm{pass}]>0$. Let $\rho_{ZZ'}$ be the resulting normalized marginal of the complementary key strings, without an additional test-statistic register. For $0<\varepsilon\le1$, define
--   $$
--   \varepsilon'=\frac{\varepsilon}{\sqrt{p_{\mathrm{pass}}}},\qquad
--   \mu=\sqrt{\frac{N}{nk}\frac{k+1}{k}\ln\frac1\varepsilon}.
--   $$
--   With purified-distance smoothing over subnormalized quantum states,
--   $$
--   H_{\max}^{\varepsilon'}(Z\mid Z')_\rho
--   \le n\,h(Q_{\mathrm{tol}}+\mu).
--   $$
--   Here $h(t)=-t\log_2t-(1-t)\log_2(1-t)$ on $0\le t\le1/2$, with $0\log_2 0=0$, and $h(t)=1$ for $t>1/2$. If $\varepsilon'\ge1$, the zero substate is allowed and the extended smooth max-entropy is $-\infty$.
--
--   This bounds the residual uncertainty of the key strings after a successful random-sample test; it makes no independent-bit assumption.
-- source:
--   Tight Finite-Key Analysis for Quantum Cryptography, arXiv:1103.4130v2, PDF p. 13, Lemma 3, Eq. (S15); proof on PDF p.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P01

namespace QAlgorithms.Papers.Independent.Intakethird100.P01

open scoped BigOperators ComplexConjugate ComplexOrder

-- Accepted extended entropy: the finite-real smoothing helper excludes radius >= 1.

open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized purifiedDistance conditionalMaxEntropy smoothConditionalMaxEntropyExtended)

noncomputable section

/-- PDF pp.13--14, Lemma 3, Eq.(S15): smooth max-entropy of the key-pair marginal
conditioned on passing, with epsilon_prime=epsilon/sqrt(p_pass). No Lambda register is
retained. For epsilon_prime>=1 the extended entropy allows the zero substate.
Source correction (printed / changed / why): S15 prints only epsilon>0; the referenced
entropy definition [53, Definition 10] restricts the smoothing radius below one at a
normalized center. We use 0<epsilon<=1 (the real domain of sqrt(log(1/epsilon))) and
explicitly extend the full subnormalized smoothing ball to all radii with EReal values.
This agrees with the referenced entropy below radius one and gives minus infinity at
radius>=1, preserving the printed epsilon_prime without an extra epsilon<sqrt(p_pass)
hypothesis. All constants and the displayed entropy inequality are unchanged. -/
theorem smoothMaxEntropyAfterPassing (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (P : StringPair (n + k) → ℝ) (hP : ∀ z, 0 ≤ P z) (hPsum : ∑ z, P z = 1)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hpass : 0 < passProbability P Q)
    (epsilon : ℝ) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    smoothConditionalMaxEntropyExtended (classicalDensity (keyLawGivenPass P Q))
        (epsilon / Real.sqrt (passProbability P Q)) ≤
      ((n : ℝ) * truncatedBinaryEntropy (Q + samplingDeviation n k epsilon) : ℝ) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P01
