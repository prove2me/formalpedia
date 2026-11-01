-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_multipartite_totalErasure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.multipartite_totalErasure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:21:50.417699+00:00
-- url     : https://prove2.me/theorems/c429cb44-2a48-47fe-b643-c1ec432edea4
-- title:
--   Section V, Eq. (16): multipartite total erasure and successive local decorrelation
-- statement:
--   Let $p\ge1$ and let $\rho_{A_1\cdots A_p}$ be a density matrix with finite positive local dimensions $d_i$. Define multipartite erasure rates by minimizing finite ensembles of product unitaries whose output on $n$ independent copies is within full trace norm $\epsilon$ of a normalized fully product state, dividing by $n\ge1$, taking $\liminf$ or $\limsup$, and then taking the supremum over $\epsilon>0$. Feasible finite costs are nonempty, bounded below, and attain their minima; normalized sequences and outer error suprema are bounded. For coordinated or independent local randomness and each of the costs $\log_2N,H(p),S_e$,
--
--   $$C_{\rm er}(\rho)=\sum_{i=1}^p S(\rho_{A_i})-S(\rho)=\sum_{j=1}^{p-1}I(A_j:A_{j+1}\cdots A_p)_\rho.$$
--
--   Moreover, for every $\epsilon>0$, eventually every $n$ admits exactly $p-1$ successive uniform local randomizations $R_j$, with stage $j$ acting only on party $j$, such that
--
--   $$\log_2N_j\le n\bigl(I(A_j:A_{j+1}\cdots A_p)_\rho+\epsilon/p\bigr),\quad\sum_j\log_2N_j\le n(C_{\rm er}(\rho)+\epsilon),$$
--
--   and the composed output is within trace norm $\epsilon$ of a fully product state. The tail information quantities are computed from actual compatible marginals of the original state. For $p=1$ the protocol is empty and the rate is zero. This states both Eq. (16) and its successive local protocol.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 10, Section V, Eq. (16): multipartite total erasure and successive local decorrelation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9--10, (16) and the protocol paragraph: total erasure and successive local decorrelation.
All three costs, both block limits, and independent/coordinated randomness have the same rate.
Only p-1 stages are used. The p=1 boundary is the empty protocol, of zero cost. -/
theorem multipartite_totalErasure {p : ℕ} (hp : 0 < p) (d : Fin p → ℕ)
    (hd : ∀ i, 0 < d i)
    (rho : Matrix (Config d) (Config d) ℂ)
    (hrho : IsDensityMatrix rho) :
    (∀ eps > (0 : ℝ), ∀ independent cost,
      (∀ n, 0 < n → (multiCosts rho n eps independent cost).Nonempty ∧
        BddBelow (multiCosts rho n eps independent cost) ∧
        sInf (multiCosts rho n eps independent cost) ∈ multiCosts rho n eps independent cost) ∧
      BddBelow (Set.range (multiBlockRate rho eps independent cost)) ∧
      BddAbove (Set.range (multiBlockRate rho eps independent cost))) ∧
    (∀ independent cost pessimistic,
      BddAbove {v | ∃ eps > (0 : ℝ),
        v = rateLimit pessimistic (multiBlockRate rho eps independent cost)} ∧
      multiErasure rho independent cost pessimistic = multiInformation rho) ∧
    (∑ j, tailInformation rho j) = multiInformation rho ∧
    (∀ eps > (0 : ℝ), ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ R : Fin (p-1) → MultiNoise (MultiCopies d n),
        (∀ j t i, i.val ≠ j.val → (R j).unitary t i = 1) ∧
        (∀ j t, (R j).weight t = ((R j).count : ℝ)⁻¹) ∧
        (∀ j, Real.logb 2 (R j).count ≤
          (n : ℝ) * (tailInformation rho j + eps / p)) ∧
        (∑ j, Real.logb 2 (R j).count) ≤ (n : ℝ) * (multiInformation rho + eps) ∧
        MultiDecorrelates (successiveBlockOutput R (multiSourcePower rho n)) eps) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
