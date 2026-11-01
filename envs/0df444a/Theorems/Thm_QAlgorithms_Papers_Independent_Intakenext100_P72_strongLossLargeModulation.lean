-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P72_strongLossLargeModulation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P72.strongLossLargeModulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:46:02.847078+00:00
-- url     : https://prove2.me/theorems/51a5675a-b691-42cb-8b5b-926e38ebd038
-- title:
--   Iterated strong-loss and large-modulation asymptotic
-- statement:
--   For $V\ge1$ and $0<G\le1$, let $C_V(G)$ and $E_V(G)$ denote the coherent and EPR signed expressions at pure-loss noise $\chi=(1-G)/G$, defined in (54) and (56). Their right-hand strong-loss coefficients agree:
--
--   $$
--   \lim_{G\downarrow0}\frac{C_V(G)}G
--   =\lim_{G\downarrow0}\frac{E_V(G)}G
--   =a(V):=\frac{1-1/V}{2\ln2},\qquad
--   \lim_{V\to\infty}a(V)=\frac1{2\ln2}.
--   $$
--
--   The normalized quotient is tested only at positive $G$. This pins the source's approximation by first taking the strong-loss coefficient at finite modulation and then taking large modulation. It does not replace the finite-$V$ coefficient by a constant or assert capacity optimality.
-- source:
--   Reverse reconciliation protocols for quantum cryptography with continuous variables, arXiv:quant-ph/0204127v1, PDF p. 5, IV.B, (59): strong-loss, large-modulation asymptotic

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P72

/-- Grosshans--Grangier, PDF p.5, IV.B, (59).
The source's approximation is the iterated strong-loss/large-modulation limit.
The G→0 limit is one-sided and excludes G=0 from the normalized quotient.
The finite-V coefficient retains the factor (1-1/V). -/
theorem strongLossLargeModulation :
    (∀ V : ℝ, 1 ≤ V →
      Tendsto (fun G : ℝ => eprExpression G ((1 - G) / G) V / G)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (strongLossCoefficient V)) ∧
      Tendsto (fun G : ℝ => coherentExpression G ((1 - G) / G) V / G)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (strongLossCoefficient V))) ∧
    Tendsto strongLossCoefficient atTop (nhds (1 / (2 * Real.log 2))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P72

end
