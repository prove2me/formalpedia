-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_compressed_exact_processor
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.compressed_exact_processor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:18:58.257975+00:00
-- url     : https://prove2.me/theorems/f68e936c-d36e-4938-919c-cdb69eff3a96
-- title:
--   Theorem 25: compression to the sum of irrep multiplicities
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. If $U$ is irreducible, there exists a fixed exact processor for all of $\mathcal T_{UV}$ with positive program dimension
--
--   $$p=d_c=\sum_{k=1}^K n_k.$$
--
--   Programs may be mixed. Neither a compression channel nor a teleportation simulator is an extra hypothesis. This gives the compressed exact construction.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 15, Theorem 25: compression to the sum of irrep multiplicities

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

/-- PDF pp.15--16, Theorem 25: exact compression to sum nk, with mixed programs.
No teleportation or compression-map existence is assumed. -/
theorem compressed_exact_processor (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat) (D : TensorIsotypicDecomposition U V) :
    0 < compressedDim D ∧
      ∃ processor : Superop (I × Fin (compressedDim D)) O,
        ProgramsChannelClass processor (covariantChannels U.mat V.mat) 0 := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
