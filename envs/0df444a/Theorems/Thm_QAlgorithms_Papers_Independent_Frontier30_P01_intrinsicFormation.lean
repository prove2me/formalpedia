-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P01_intrinsicFormation
-- name    : QAlgorithms.Papers.Independent.Frontier30.P01.intrinsicFormation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:27:17.908044+00:00
-- url     : https://prove2.me/theorems/5572405a-a0b8-4ba6-a1a7-1da3d2608e46
-- title:
--   Classical intrinsic information is bounded by formation of the embedding
-- statement:
--   Let $p_{ijk}$ be a probability distribution on finite nonempty alphabets for Alice, Bob and Eve. Suppose that for each pair $(i,j)$ there is at most one $k$ with $p_{ijk}>0$. Define
--
--   $$
--   |\psi_p\rangle=\sum_{i,j,k}\sqrt{p_{ijk}}\,|ijk\rangle,
--   \qquad \rho_{AB}=\operatorname{Tr}_E|\psi_p\rangle\langle\psi_p|.
--   $$
--
--   Let $I(A:B\downarrow E)_p$ be the infimum of $I(A:B\mid L)$ over every stochastic channel from Eve's alphabet to an arbitrary finite nonempty alphabet $L$. Let $E_F$ be entanglement of formation, the convex roof of marginal entropy over normalized pure-state ensembles. In bit units,
--
--   $$
--   I(A:B\downarrow E)_p\le E_F(\rho_{AB}).
--   $$
--
--   The bound relates the classical intrinsic information to entanglement in the prescribed positive-amplitude embedding; it does not optimize over embeddings or replace the classical quantity by its quantum extension.
-- source:
--   Unifying classical and quantum key distillation, arXiv:quant-ph/0608199v3, PDF p. 14, theorem-4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P01

namespace QAlgorithms.Papers.Independent.Frontier30.P01

open scoped Matrix ComplexConjugate

noncomputable section

/-- arXiv:quant-ph/0608199v3, PDF pp.14--15, Theorem 4.3, Eq.(40).
Formation uses the accepted convex roof over normalized PURE ensembles. -/
theorem intrinsicFormation {a b e : ℕ} (ha : 0 < a) (hb : 0 < b) (he : 0 < e)
    (p : ((Fin a × Fin b) × Fin e) → ℝ) (hnonneg : ∀ x, 0 ≤ p x)
    (htotal : ∑ x, p x = 1) (hdet : EveDetermined p) :
    classicalIntrinsic p ≤ Information100.P08.formation
      (traceRight (pureDensity (qqqVector p))) := by sorry

end

end QAlgorithms.Papers.Independent.Frontier30.P01
