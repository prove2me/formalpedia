-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_strict_compression_comparison
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.strict_compression_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:21:44.208988+00:00
-- url     : https://prove2.me/theorems/f45cab49-386b-4469-aed4-4146a6ab3d6b
-- title:
--   Remark 26: when compression strictly improves the uncompressed bound
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. For this physical decomposition,
--
--   $$\sum_k n_k<d_1d_2\ \Longleftrightarrow\ \exists k,\ b_k>1,\qquad \sum_k n_k=d_1d_2\ \Longleftrightarrow\ \forall k,\ b_k=1.$$
--
--   Positive multiplicities and the unitary decomposition give $\sum_k b_kn_k=d_1d_2$. Thus the comparison concerns program memory in Theorem 25 versus Proposition 24; it is not a run-time claim.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 16, Remark 26: when compression strictly improves the uncompressed bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section General

variable {G I O : Type*} [Group G] [TopologicalSpace G]

variable [Fintype I] [DecidableEq I] [inputNonempty : Nonempty I]

variable [Fintype O] [DecidableEq O] [outputNonempty : Nonempty O]

include inputNonempty outputNonempty

/-- PDF p.16, Remark 26: strict improvement and the equality case, with
positive multiplicities and a physical unitary decomposition. -/
theorem strict_compression_comparison (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (D : TensorIsotypicDecomposition U V) :
    (compressedDim D < Fintype.card I * Fintype.card O ↔
      ∃ k, 1 < D.degree k) ∧
    (compressedDim D = Fintype.card I * Fintype.card O ↔
      ∀ k, D.degree k = 1) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
