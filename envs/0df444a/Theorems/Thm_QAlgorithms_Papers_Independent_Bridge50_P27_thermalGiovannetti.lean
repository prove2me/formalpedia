-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_thermalGiovannetti
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.thermalGiovannetti
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:18:26.996141+00:00
-- url     : https://prove2.me/theorems/9b3b7104-83b8-4104-a5d0-36bc74f03133
-- title:
--   Thermal Giovannetti strong converse with corrected finite-block exponent
-- statement:
--   Let $n\ge1$ be the number of independent physical uses and $M\ge1$ the number of equiprobable messages. A code consists of arbitrary positive trace-class, trace-one states on the complete $n$-mode Fock space and a positive finite POVM summing to the identity. Codewords may be entangled across uses. Write $R_n=\log_2(M)/n$ and $s_n$ for its average decoding success. Let $\Pi_L$ project onto number strings of total occupation at most $L$, inclusively. The maximum occupation condition is $M^{-1}\sum_m\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho_m)\ge1-\delta_1(n)$, where $0\le\delta_1(n)\le1$ and $\delta_1(n)\to0$. This constraint is on the average code density. All logarithms and rates are in bits, and $g(x)=(x+1)\log_2(x+1)-x\log_2x$, with $g(0)=0$. Fix $0\le\eta\le1$, $N_B,N_S\ge0$. For every fixed $d,d_5>0$, define $b_2(d_5)=g(\eta N_S+(1-\eta)N_B+d_5)-\log_2(1+2(1-\eta)N_B)$. There are a nonnegative tail $d_6(n)\to0$ and a threshold $n_0>1$, independent of codes and deficits, such that
--
--   $$s_n\le2^{-n[R_n-b_2(d_5)-\log_2(n)/n-d]}+\frac1n+2\sqrt{\delta_1(n)+2\sqrt{\delta_1(n)}+d_6(n)}\qquad(n\ge n_0).$$
--
--   For every fixed $R>b_2(0)$ and every maximum occupation family with eventually $R_n\ge R$, $s_n\to0$.
--
--   This gives the finite-block and operational limiting forms of bound (7). The sign before $\log_2(n)/n$ is corrected using the preceding valid inequality on PDF p.17; independent moderation is required.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 15, Theorem 2 / §5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P27

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

-- Exact accepted definitions, checked against their complete source bodies.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)

open QAlgorithms.Papers.Independent.Renew46.P30 (photonTotal)

open QAlgorithms.Papers.Independent.Support50.P06 (totalEnergy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2, PDF pp.15–18. CORRECTION: printed +log2(n)/n in the negative
bracket is replaced by -log2(n)/n: the preceding valid p.17 inequality has
+log2(1/epsilon) OUTSIDE -H2. At epsilon=1/n this costs a factor n.
The output slack d5 is per use and fixed before the uniform n0. -/
theorem thermalGiovannetti (eta NB NS : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hNB : 0 ≤ NB) (hNS : 0 ≤ NS) :
    (∀ d d5 : ℝ, 0 < d → 0 < d5 →
      ∃ d6 : ℕ → ℝ, (∀ n, 0 ≤ d6 n) ∧ Tendsto d6 atTop (𝓝 0) ∧
      ∃ n0 : ℕ, 1 < n0 ∧ ∀ n ≥ n0, ∀ M : ℕ, ∀ K : FockCommunicationCode n M,
        ∀ deficit : ℝ, 0 ≤ deficit → deficit ≤ 1 →
        1 - deficit ≤ codeShadow K NS →
        decodingSuccessProbability (.thermal eta NB) K ≤
          Real.rpow 2 (-(n : ℝ) *
            (communicationRateBits n M - (bosonicEntropy (outputMean (.thermal eta NB) NS + d5) -
              logBits (1 + 2 * (1 - eta) * NB)) - logBits n / (n : ℝ) - d)) +
            1 / (n : ℝ) + 2 * Real.sqrt (deficit + 2 * Real.sqrt deficit + d6 n)) ∧
      StrongConverse (.thermal eta NB) NS (giovannettiRateBound (.thermal eta NB) NS) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
