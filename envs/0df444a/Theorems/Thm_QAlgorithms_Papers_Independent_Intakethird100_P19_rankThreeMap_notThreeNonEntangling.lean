-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_rankThreeMap_notThreeNonEntangling
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.rankThreeMap_notThreeNonEntangling
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:44:07.697132+00:00
-- url     : https://prove2.me/theorems/2f29afd2-a9d9-4571-9a15-69e26399ea32
-- title:
--   Proposition 21: rank-three detector channels are not 3-non-entangling
-- statement:
--   All registers are finite-dimensional complex spaces with positive local dimensions and fixed product bases. Let $d\ge3$ and $(d-3)/3<\beta\le(d-2)/2$, and let $\rho_d(\beta)=[I-(\beta+1)F_d/d]/[d^2-(\beta+1)]$ be the Werner state. For every unit ket $\eta$ of Schmidt rank three such that $\operatorname{Tr}(\rho_d(\beta)W_\eta)<0$, construct
--
--   $$W_\eta=(|\eta\rangle\langle\eta|)^\Gamma,\qquad A_\eta=(W_\eta+2I)/3,\qquad \Lambda_\eta(X)=\operatorname{Tr}(A_\eta X)I_4/4+\operatorname{Tr}((I-A_\eta)X)\phi_2^+.$$
--
--   Then $\Lambda_\eta$ is a channel, is dually non-entangling, has PPT grouped Choi operator, sends $\rho_d(\beta)$ to an LOCC-distillable two-qubit state, and is not $3$-non-entangling. Dually non-entangling means that the channel and its trace dual preserve the separable positive cone; $3$-non-entangling tests preservation after adjoining a three-dimensional identity ancilla at each party. LOCC-distillability is trace-norm convergence of deterministic LOCC outputs on tensor powers to $\phi_2^+$.
--
--   The same conclusions are also explicitly recorded for the canonical detector $\eta=(|00\rangle+|11\rangle+|22\rangle)/\sqrt3$ in the first three local coordinates.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 23, Proposition 21

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Proposition 21, PDF p.23: the Eq.(21) channels for every unit
Schmidt-rank-three detector of the Werner state are not 3-NE. The rank
and negative pairing specify the detector used in the source proof; all
channel, preservation and distillability properties remain conclusions.
The canonical equal-amplitude detector is also recorded explicitly. -/
theorem rankThreeMap_notThreeNonEntangling (d : ℕ) (hd : 3 ≤ d)
    (beta : ℝ) (hlo : ((d : ℝ) - 3) / 3 < beta)
    (hhi : beta ≤ ((d : ℝ) - 2) / 2) :
    (IsChannel (rankThreeMap d) ∧ DNE (rankThreeMap d) ∧ ChoiPPT (rankThreeMap d) ∧
      LOCCDistillable (rankThreeMap d (betaWernerState d beta)) ∧ ¬ KNE 3 (rankThreeMap d)) ∧
    ∀ eta : UnitBipartiteKet d d, finiteSchmidtRank eta.ket = 3 →
      (betaWernerState d beta * partialTransposeFirst eta.rho).trace.re < 0 →
      let L := witnessMap (partialTransposeFirst eta.rho)
      IsChannel L ∧ DNE L ∧ ChoiPPT L ∧
        LOCCDistillable (L (betaWernerState d beta)) ∧ ¬ KNE 3 L := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
