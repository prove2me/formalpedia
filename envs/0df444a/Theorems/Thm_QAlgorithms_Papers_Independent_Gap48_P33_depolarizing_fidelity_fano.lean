-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P33_depolarizing_fidelity_fano
-- name    : QAlgorithms.Papers.Independent.Gap48.P33.depolarizing_fidelity_fano
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:40:48.442996+00:00
-- url     : https://prove2.me/theorems/af19a77e-940c-4322-8625-7b9a2c2d4724
-- title:
--   depolarizing fidelity and saturation of Schumacher Fano
-- statement:
--   For $p,q\in[0,1]$, let $F_e$ be the squared purification overlap after applying $\mathcal N_p$ to the input $|\Psi_-(q)\rangle=\sqrt{1-q}|10\rangle-\sqrt q|01\rangle$ of (5.4), with signal first. Then
--
--   $$F_e(p,q)=1-p+\frac p3(1-2q)^2.$$
--
--   At $q=1/2$, $F_e=1-p$ and
--
--   $$S(Q'R)=H_2(F_e)+(1-F_e)\log_2 3.$$
--
--   This is equality in Schumacher's exchange-entropy Fano inequality (3.39), distinct from the doubled loss inequality (3.42).
--
--   Here $H_2$ denotes binary Shannon entropy in bits, with $0\log 0=0$.
-- source:
--   On the von Neumann capacity of noisy quantum channels, arXiv:quant-ph/9609024v3, PDF p. 11, V.A, (5.19): depolarizing fidelity and saturation of Schumacher Fano

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

namespace QAlgorithms.Papers.Independent.Gap48.P33

open scoped BigOperators Matrix ComplexConjugate

-- Reuse only definitions from the pinned accepted library; no imported theorem is used.

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average labelInformation)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first both)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

open QAlgorithms.Papers.Independent.Claimed50.P03 (pauliWeight wordSupport)

/-- PDF p.11, (5.19): Schumacher's EXCHANGE-entropy inequality (3.39) is saturated. -/
theorem depolarizing_fidelity_fano (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    referenceFidelity (pauliDepolarizing p) (qBasis 0 q) = 1 - p + (p / 3) * (1 - 2 * q) ^ 2 ∧
    referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2)) = 1 - p ∧
    vnEntropy (depolarizingOutput p (1 / 2)) =
      binEntropy2 (referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2))) +
        (1 - referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2))) * Real.logb 2 3 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P33
