-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_totalInformation_zero_iff_product
-- name    : QAlgorithms.Papers.Independent.Support50.P09.totalInformation_zero_iff_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:58:47.965227+00:00
-- url     : https://prove2.me/theorems/df183564-9199-44a4-8935-bed33e2c4148
-- title:
--   Unnumbered correlation criterion following Definition IV.1
-- statement:
--   Let $\rho$ be one normalized density operator on finitely many finite nonzero registers. All named systems below are disjoint groups of these registers, and every entropy is computed from the corresponding marginal of $\rho$. Define $I(Y_1;\ldots;Y_r\mid E)=\sum_j H(Y_jE)-H(Y_1\cdots Y_rE)-(r-1)H(E)$, with logarithms to base two; omitting $E$ denotes unconditional information. Empty groups represent one-dimensional systems.
--
--   For $m\ge1$ and a state on $X_1\cdots X_m$, let $\rho^{X_i}$ be its own single-party marginals. Then
--   $$
--   I(X_1;\cdots;X_m)_\rho=0\quad\Longleftrightarrow\quad
--   \rho=\rho^{X_1}\otimes\cdots\otimes\rho^{X_m}.
--   $$
--
--   This characterizes absence of total correlation, rather than absence of squashed entanglement.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 14, Unnumbered correlation criterion following Definition IV.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnumbered criterion after Definition IV.1, PDF pp.13–14:
zero TOTAL correlation iff the state equals the product of its own marginals. -/
theorem totalInformation_zero_iff_product {m : ℕ} (hm : 0 < m)
    {D : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    info .total rho (singleParties m) ∅ = 0 ↔ rho = productOfMarginals rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
