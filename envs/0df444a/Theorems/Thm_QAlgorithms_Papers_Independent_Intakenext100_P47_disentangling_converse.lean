-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_disentangling_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.disentangling_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:17:46.609657+00:00
-- url     : https://prove2.me/theorems/7b31f51b-6458-4229-bfa1-c935ed57f05b
-- title:
--   Proposition III.1: approximate disentangling converse
-- statement:
--   Let $\rho_{AB}$ be a density matrix on finite nonzero spaces, $d=d_Ad_B$, $n\ge1$, and $\epsilon\ge0$. Suppose $T$ is a finite coordinated product-unitary ensemble with probabilities $p_i$ and $N$ terms whose output on $\rho^{\otimes n}$ is within full trace norm $\epsilon$ of a normalized separable state. Let $\mathcal F$ consist of all pairs $(R,\sigma)$ with $R$ any COLUR map on the $n$ copies, $\sigma$ separable and normalized, and $\|\sigma-R(\rho^{\otimes n})\|_1\le\epsilon$. Then $\mathcal F$ is nonempty, its following entropy objective is bounded below, and
--
--   $$\log_2N\ge H(p)\ge S_e(T,\rho^{\otimes n})\ge\inf_{(R,\sigma)\in\mathcal F}\bigl(S(\sigma)-nS(\rho)-n\epsilon\log_2d-\eta(\epsilon)\bigr).$$
--
--   The final $\eta(\epsilon)$ has no factor $n$. This is the approximate disentangling converse and optimizes over all channels and targets, rather than targets near one fixed channel.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 6, Proposition III.1: approximate disentangling converse

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

/-- PDF p.6, Proposition III.1: optimization includes R as well as its separable target.
The final erasureEta(eps) is not multiplied by n. -/
theorem disentangling_converse {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (n : ℕ) (hn : 0 < n) (eps : ℝ) (heps : 0 ≤ eps)
    (T : COLUR (Copies A n) (Copies B n))
    (hT : Disentangles (T.operation (sourcePower rho n)) eps) :
    (separableEntropyCosts rho n eps).Nonempty ∧
    BddBelow (separableEntropyCosts rho n eps) ∧
    sInf (separableEntropyCosts rho n eps) ≤ entropyExchange T.operation (sourcePower rho n) ∧
    entropyExchange T.operation (sourcePower rho n) ≤ shannon T.weight ∧
    shannon T.weight ≤ Real.logb 2 T.count := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
