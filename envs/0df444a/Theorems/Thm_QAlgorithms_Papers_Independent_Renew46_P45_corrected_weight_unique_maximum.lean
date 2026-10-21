-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P45_corrected_weight_unique_maximum
-- name    : QAlgorithms.Papers.Independent.Renew46.P45.corrected_weight_unique_maximum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:46:16.844537+00:00
-- url     : https://prove2.me/theorems/850b8a09-35d3-46d4-9180-bfbe78fbee6b
-- title:
--   Unique maximum on the corrected nonnegative weight domain
-- statement:
--   Let $d\ge2$, $N\ge1$ and $M\ge0$ be integers. Let $W_1$ consist of pairs of integer tuples $(m,\mu)\in\mathbb Z^d\times\mathbb Z^d$ satisfying $m_1\ge\cdots\ge m_d\ge0$, $\mu_j\ge0$ for every $j$, $\sum_jm_j=M$, $\sum_j\mu_j=N$, and $\mu_j\le m_j-m_{j+1}$ for $j<d$. Define
--   $$
--   F_2(m,\mu)=\sum_{j=1}^d\mu_j(2m_j-2j-\mu_j).
--   $$
--   The pair $m^*=(M,0,\ldots,0)$ and
--   $$
--   \mu^*=\begin{cases}(N,0,\ldots,0),&N\le M,\\(M,0,\ldots,0,N-M),&N>M\end{cases}
--   $$
--   is feasible and is the unique maximizer:
--   $$
--   F_2(m,\mu)\le F_2(m^*,\mu^*),\qquad F_2(m,\mu)=F_2(m^*,\mu^*)\iff(m,\mu)=(m^*,\mu^*).
--   $$
--   Both regimes are included, and the two branch formulas agree at $N=M$. This finite weight optimization underlies the general-dimensional cloning coefficient bound.
--
--   **Source Correction** Printed $W_1$ omits $m_d\ge0$ and $\mu_d\ge0$, and nearby prose prints $m_d>0$. The proof on p.10 and the nonnegative Pieri increments require the domain stated here. The literal printed domain has counterexamples. Independent moderation of this correction remains required.
-- source:
--   Optimal Cloning of Pure States, Judging Single Clones, arXiv:quant-ph/9807010v1, PDF p. 10, Lemma 6; Eq.(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45

noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable

/-- PDF pp.9–10 Eq.(27), Lemma 6: unique maximum on corrected NONNEGATIVE
W_1. Printed W_1 omits m_d≥0,mu_d≥0 and prose prints m_d>0; the proof on p.10
and Appendix A3 require the corrections. N≥1 is essential to uniqueness.
No global cloning constraint M>N is imposed on this local lemma. -/
theorem corrected_weight_unique_maximum (d N M : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    IsWeightFeasible d N M (symmetricWeight d M) (maximizingRemoval d N M) ∧
    ∀ m mu : Fin d → ℤ, IsWeightFeasible d N M m mu →
      weightObjective m mu ≤ weightObjective (symmetricWeight d M) (maximizingRemoval d N M) ∧
      (weightObjective m mu = weightObjective (symmetricWeight d M) (maximizingRemoval d N M) ↔
        m = symmetricWeight d M ∧ mu = maximizingRemoval d N M) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P45

end
