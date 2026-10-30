-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_thermalKoenigSmith
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.thermalKoenigSmith
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:17:32.734308+00:00
-- url     : https://prove2.me/theorems/86fee52e-af78-465f-b4ff-9cd9cd98ae51
-- title:
--   Thermal Koenig–Smith strong converse: finite-block and limiting bounds
-- statement:
--   Let $n\ge1$ be the number of independent physical uses and $M\ge1$ the number of equiprobable messages. A code consists of arbitrary positive trace-class, trace-one states on the complete $n$-mode Fock space and a positive finite POVM summing to the identity. Codewords may be entangled across uses. Write $R_n=\log_2(M)/n$ and $s_n$ for its average decoding success. Let $\Pi_L$ project onto number strings of total occupation at most $L$, inclusively. The maximum occupation condition is $M^{-1}\sum_m\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho_m)\ge1-\delta_1(n)$, where $0\le\delta_1(n)\le1$ and $\delta_1(n)\to0$. This constraint is on the average code density. All logarithms and rates are in bits, and $g(x)=(x+1)\log_2(x+1)-x\log_2x$, with $g(0)=0$. Fix $0\le\eta\le1$, $N_B,N_S\ge0$. Set $b_1=g(\eta N_S/[(1-\eta)N_B+1])$. For every fixed $d_2,d_3>0$ there are a nonnegative tail $d_4(n)\to0$ and a positive threshold $n_0$, uniform over all codes and deficits, such that for every $n\ge n_0$ satisfying the occupation constraint,
--
--   $$s_n\le2^{-n(R_n-b_1-d_2-d_3)}+2\sqrt{\delta_1(n)+d_4(n)}+2\sqrt{\delta_1(n)}.$$
--
--   For every fixed $R>b_1$ and every such family with eventually $R_n\ge R$, $s_n\to0$.
--
--   This strengthens bound (8) to an operational strong converse under the maximum occupation constraint.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 10, Theorem 1 / §5.1

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

/-- Theorem 1, PDF pp.10–11. Both the finite-block estimate and its all-family
limiting conclusion are retained. The d4 tail and eventual threshold precede
all codes and deficits. Entropy slack d2 is obtained by continuity, not by
assuming g is 1-Lipschitz near zero. -/
theorem thermalKoenigSmith (eta NB NS : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hNB : 0 ≤ NB) (hNS : 0 ≤ NS) :
    (∀ d2 d3 : ℝ, 0 < d2 → 0 < d3 →
      ∃ d4 : ℕ → ℝ, (∀ n, 0 ≤ d4 n) ∧ Tendsto d4 atTop (𝓝 0) ∧
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∀ M : ℕ, ∀ K : FockCommunicationCode n M,
        ∀ deficit : ℝ, 0 ≤ deficit → deficit ≤ 1 →
        1 - deficit ≤ codeShadow K NS →
        decodingSuccessProbability (.thermal eta NB) K ≤
          Real.rpow 2 (-(n : ℝ) * (communicationRateBits n M - lossBound (.thermal eta NB) NS - d2 - d3)) +
            2 * Real.sqrt (deficit + d4 n) + 2 * Real.sqrt deficit) ∧
      StrongConverse (.thermal eta NB) NS (lossBound (.thermal eta NB) NS) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
