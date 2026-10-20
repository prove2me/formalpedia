-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P01_intrinsicEntanglementCost
-- name    : QAlgorithms.Papers.Independent.Frontier30.P01.intrinsicEntanglementCost
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:28:26.736318+00:00
-- url     : https://prove2.me/theorems/c73ce7a2-3fc9-41e0-b781-9d3c59aad059
-- title:
--   Classical intrinsic information is bounded by entanglement cost of the embedding
-- statement:
--   Let $p_{ijk}$ be a probability distribution on finite nonempty alphabets such that each positive-probability pair $(i,j)$ determines Eve's value $k$. Let $|\psi_p\rangle=\sum_{i,j,k}\sqrt{p_{ijk}}|ijk\rangle$, and set $\rho_{AB}=\operatorname{Tr}_E|\psi_p\rangle\langle\psi_p|$. Classical intrinsic information is minimized over stochastic processing of Eve, and $E_C$ denotes the operational singlet formation cost under finite adaptive LOCC with vanishing trace-distance error. Both quantities are in bits. Then
--
--   $$
--   I(A:B\downarrow E)_p\le E_C(\rho_{AB}).
--   $$
--
--   This extends Theorem 4.3 from formation to asymptotic entanglement cost. The formal statement uses the accepted operational formation-cost definition, rather than assuming a numerical value or a regularization identity as a hypothesis.
-- source:
--   Unifying classical and quantum key distillation, arXiv:quant-ph/0608199v3, PDF p. 15, intrinsic-entanglement-cost

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

namespace QAlgorithms.Papers.Independent.Frontier30.P01

open scoped Matrix ComplexConjugate

noncomputable section

/-- arXiv:quant-ph/0608199v3, PDF p.15, unnumbered extension of Theorem 4.3.
The right side is the accepted operational singlet formation cost under finite
adaptive LOCC and half trace distance, rather than a free regularization score. -/
theorem intrinsicEntanglementCost {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (p : ((Fin a × Fin b) × Fin e) → ℝ) (hnonneg : ∀ x, 0 ≤ p x)
    (htotal : ∑ x, p x = 1) (hdet : EveDetermined p) :
    classicalIntrinsic p ≤ Dependency50.P42.entanglementCost
      Dependency50.P42.halfTraceDistance
      (traceRight (pureDensity (qqqVector p))) := by sorry

end

end QAlgorithms.Papers.Independent.Frontier30.P01
