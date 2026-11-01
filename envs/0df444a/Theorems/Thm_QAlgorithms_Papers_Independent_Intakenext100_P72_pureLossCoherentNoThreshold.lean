-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P72_pureLossCoherentNoThreshold
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P72.pureLossCoherentNoThreshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:45:04.892859+00:00
-- url     : https://prove2.me/theorems/0ea0ff18-9678-4f96-9280-16edcbdcbee4
-- title:
--   Positive pure-loss coherent model balance at every nonzero transmission
-- statement:
--   Let $0<G\le1$ and $V>1$, and set $\chi=(1-G)/G$. Define the signed coherent and EPR model expressions by
--
--   $$
--   C=\frac12\log_2\frac1{(G\chi+G/V)(G\chi+G)},\qquad
--   E=\frac14\log_2\frac1{(G\chi+G/V)^2}.
--   $$
--
--   For the positive root $T_G(s)=(\sqrt{G^2s^2+4}-Gs)/2$, the source's high-modulation coherent inequality $1-G<T_G(1)$ holds. The finite-modulation product also satisfies $(G\chi+G)(G\chi+G/V)<1$, and
--
--   $$
--   C=E=\frac12\log_2\frac1{1-G(1-1/V)}>0.
--   $$
--
--   These signed model expressions remain positive for arbitrarily small positive $G$. The statement excludes both zero transmission and zero coherent modulation; it asserts no loss-independent positive yield and no general attack reduction.
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, PDF p. 4, III.C, (53): pure-loss coherent protocols have no 3 dB threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- Grosshans--Grangier, PDF p.4, III.C, (53), linked to the finite-V
expressions (44), (54)--(57). Positive transmission and nonzero coherent
modulation are explicit; no positive rate is asserted at G=0. -/
theorem pureLossCoherentNoThreshold
    (G V : ℝ) (hG : 0 < G) (hGloss : G ≤ 1) (hV : 1 < V) :
    1 - G < noiseThreshold G 1 ∧
    varianceProduct G ((1 - G) / G) V 1 < 1 ∧
    0 < coherentExpression G ((1 - G) / G) V ∧
    coherentExpression G ((1 - G) / G) V = eprExpression G ((1 - G) / G) V ∧
    coherentExpression G ((1 - G) / G) V = lossExpression G V := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P72

end
