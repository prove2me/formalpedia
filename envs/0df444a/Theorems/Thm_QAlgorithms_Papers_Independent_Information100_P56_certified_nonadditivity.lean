-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_certified_nonadditivity
-- name    : QAlgorithms.Papers.Independent.Information100.P56.certified_nonadditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:27:57.564706+00:00
-- url     : https://prove2.me/theorems/34934ba2-a043-45f3-a2e6-7d289561d8d6
-- title:
--   Theorem VIII.1: certified two-use nonadditivity
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. In the hybrid binary channel, Bob has the binary symmetric channel of crossover $q$, while Eve receives $|\psi_b\rangle=\sqrt{q^{\prime}}|0\rangle+(-1)^b\sqrt{1-q^{\prime}}|1\rangle$. Here $q,q^{\prime}\in[0,1]$, and $x$ is the probability of input symbol $1$. Write $h$ for natural binary entropy. Set $q=q^{\prime}=p=621/5000$ exactly. For the exact laws $P_1=(364,217,217,202)/1000$ and $P_3=(0,1/2,1/2,0)$ in order $(00,01,10,11)$, define $R=[\Delta_2(P_3*P_1)-\Delta_2(P_1)]/2$. Then
--
--   $$C^{(1)}=0,\qquad\frac1{1000000}<R<\frac{11}{10000000},\qquad C^{(2)}\ge2R>0=2C^{(1)}.$$
--
--   This certifies strict two-use nonadditivity. The entropy certificates and single-use converse are not assumed as hypotheses.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 22, Theorem VIII.1: certified two-use nonadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Theorem VIII.1, pp.22–24: certified two-use nonadditivity with exact rational
parameters and the source's coset outer law. Entropy certificates are conclusions of
this source result, never hypotheses of the single-use converse. -/
theorem certified_nonadditivity :
    privateInfo (hybridBob (621 / 5000)) (hybridEve (621 / 5000)) = 0 ∧
    (1 : ℝ) / 1000000 < witnessRate ∧ witnessRate < (11 : ℝ) / 10000000 ∧
    2 * witnessRate ≤ blockPrivate 2 (hybridBob (621 / 5000)) (hybridEve (621 / 5000)) ∧
    0 < blockPrivate 2 (hybridBob (621 / 5000)) (hybridEve (621 / 5000)) ∧
    2 * privateInfo (hybridBob (621 / 5000)) (hybridEve (621 / 5000)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
