-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_conditionalInformation_chain
-- name    : QAlgorithms.Papers.Independent.Support50.P09.conditionalInformation_chain
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T19:01:38.836003+00:00
-- url     : https://prove2.me/theorems/eebea2fb-625c-4de3-b1e5-e4f78af2565e
-- title:
--   Lemma IV.4 (Chain-type Rule)
-- statement:
--   Let $\rho$ be one normalized density operator on finitely many finite nonzero registers. All named systems below are disjoint groups of these registers, and every entropy is computed from the corresponding marginal of $\rho$. Define $I(Y_1;\ldots;Y_r\mid E)=\sum_j H(Y_jE)-H(Y_1\cdots Y_rE)-(r-1)H(E)$, with logarithms to base two; omitting $E$ denotes unconditional information. Empty groups represent one-dimensional systems.
--
--   For disjoint $A,A',X_1,\ldots,X_m,E$, with $m\ge0$,
--   $$
--   I(AA';X_1;\ldots;X_m\mid E)\ge I(A;X_1;\ldots;X_m\mid A'E).
--   $$
--
--   This transfers the removed register into the conditioning system. It is distinct from disposal with unchanged conditioning.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 15, Lemma IV.4 (Chain-type Rule)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma IV.4, PDF p.15, (38): move A' into the conditioning system.
Includes zero X registers, when both one-party expressions vanish. -/
theorem conditionalInformation_chain {n m : ℕ} {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (a ap e : Finset (Fin n)) (x : Fin m → Finset (Fin n))
    (hdis : DisjointRegisters (Fin.cons a (Fin.cons ap x)) e) :
    info .total rho (Fin.cons a x) (ap ∪ e) ≤
      info .total rho (Fin.cons (a ∪ ap) x) e := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
