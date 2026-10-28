-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_conditionalInformation_discard
-- name    : QAlgorithms.Papers.Independent.Support50.P09.conditionalInformation_discard
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:00:50.183879+00:00
-- url     : https://prove2.me/theorems/a052eafa-8ae9-48a9-9115-11e948a07b37
-- title:
--   Lemma IV.3 (Monotonicity of conditional multiparty information)
-- statement:
--   Let $\rho$ be one normalized density operator on finitely many finite nonzero registers. All named systems below are disjoint groups of these registers, and every entropy is computed from the corresponding marginal of $\rho$. Define $I(Y_1;\ldots;Y_r\mid E)=\sum_j H(Y_jE)-H(Y_1\cdots Y_rE)-(r-1)H(E)$, with logarithms to base two; omitting $E$ denotes unconditional information. Empty groups represent one-dimensional systems.
--
--   For disjoint $A,B,X_1,\ldots,X_m,E$, with $m\ge0$,
--   $$
--   I(AB;X_1;\ldots;X_m\mid E)\ge I(A;X_1;\ldots;X_m\mid E).
--   $$
--
--   Discarding $B$ cannot increase conditional total correlation, with $E$ unchanged.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 14, Lemma IV.3 (Monotonicity of conditional multiparty information)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma IV.3, PDF p.14, (37): discard B and KEEP E unchanged.
The proof's dropped E in one expansion does not alter the stated inequality. -/
theorem conditionalInformation_discard {n m : ℕ} {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (a b e : Finset (Fin n)) (x : Fin m → Finset (Fin n))
    (hdis : DisjointRegisters (Fin.cons a (Fin.cons b x)) e) :
    info .total rho (Fin.cons a x) e ≤ info .total rho (Fin.cons (a ∪ b) x) e := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
