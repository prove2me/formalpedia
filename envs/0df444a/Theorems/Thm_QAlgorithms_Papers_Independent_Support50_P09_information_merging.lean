-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P09_information_merging
-- name    : QAlgorithms.Papers.Independent.Support50.P09.information_merging
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:59:38.187158+00:00
-- url     : https://prove2.me/theorems/ee8cbd53-675c-4429-bf87-133e4c0eaa08
-- title:
--   Lemma IV.2 (Merging of multiparty information terms)
-- statement:
--   Let $\rho$ be one normalized density operator on finitely many finite nonzero registers. All named systems below are disjoint groups of these registers, and every entropy is computed from the corresponding marginal of $\rho$. Define $I(Y_1;\ldots;Y_r\mid E)=\sum_j H(Y_jE)-H(Y_1\cdots Y_rE)-(r-1)H(E)$, with logarithms to base two; omitting $E$ denotes unconditional information. Empty groups represent one-dimensional systems.
--
--   Let $A,B,X_1,\ldots,X_m$ be disjoint systems, allowing $m=0$. Then
--   $$
--   I(A;B;X_1;\ldots;X_m)-I(A;B)=I(AB;X_1;\ldots;X_m).
--   $$
--
--   The register $B$ is merged into $A$, preserving its correlations.
-- source:
--   Distributed Compression and Multiparty Squashed Entanglement, arXiv:0707.2792v2, PDF p. 14, Lemma IV.2 (Merging of multiparty information terms)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P09

open QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma IV.2, PDF p.14, (36): merge A and B without discarding B.
There may be zero other X registers. -/
theorem information_merging {n m : ℕ} {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho)
    (a b : Finset (Fin n)) (x : Fin m → Finset (Fin n))
    (hdis : DisjointRegisters (Fin.cons a (Fin.cons b x)) ∅) :
    info .total rho (Fin.cons a (Fin.cons b x)) ∅ - info .total rho ![a,b] ∅ =
      info .total rho (Fin.cons (a ∪ b) x) ∅ := by sorry

end QAlgorithms.Papers.Independent.Support50.P09

end
