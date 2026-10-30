-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_additiveKoenigSmith
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.additiveKoenigSmith
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:19:17.58601+00:00
-- url     : https://prove2.me/theorems/e0b013b7-6b06-4ced-84e7-264d0b73bdeb
-- title:
--   Additive Koenig–Smith-like strong converse
-- statement:
--   Let $n\ge1$ be the number of independent physical uses and $M\ge1$ the number of equiprobable messages. A code consists of arbitrary positive trace-class, trace-one states on the complete $n$-mode Fock space and a positive finite POVM summing to the identity. Codewords may be entangled across uses. Write $R_n=\log_2(M)/n$ and $s_n$ for its average decoding success. Let $\Pi_L$ project onto number strings of total occupation at most $L$, inclusively. The maximum occupation condition is $M^{-1}\sum_m\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho_m)\ge1-\delta_1(n)$, where $0\le\delta_1(n)\le1$ and $\delta_1(n)\to0$. This constraint is on the average code density. All logarithms and rates are in bits, and $g(x)=(x+1)\log_2(x+1)-x\log_2x$, with $g(0)=0$. Fix additive noise variance $v\ge0$ and $N_S\ge0$, including the identity channel at $v=0$. For every fixed rate above the threshold and every code family satisfying the occupation condition,
--
--   $$R>g\!\left(\frac{N_S}{v+1}\right),\quad R_n\ge R\text{ eventually}\quad\Longrightarrow\quad s_n\longrightarrow0.$$
--
--   This is bound (13) as an all-code strong converse. The threshold follows the loss-then-amplifier decomposition with transmissivity $1/(v+1)$, so there is no additional thermal transmissivity in its numerator.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 12, §5.2

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

/-- Section 5.2, PDF p.12, threshold (13). Includes the zero-noise identity.
The numerator is NS, with no residual eta from the thermal parametrization. -/
theorem additiveKoenigSmith (v NS : ℝ) (hv : 0 ≤ v) (hNS : 0 ≤ NS) :
    StrongConverse (.additive v) NS (bosonicEntropy (NS / (v + 1))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
