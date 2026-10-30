-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_pure_program_upper_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.pure_program_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:25:21.52888+00:00
-- url     : https://prove2.me/theorems/ad1cd37e-ce28-4481-b3f1-82d0cf18026b
-- title:
--   §5: pure-program upper bound from purification
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. If $U$ is irreducible, there is a fixed exact processor for all covariant channels using unit pure programs with program dimension
--
--   $$p=d_c^2.$$
--
--   If the actual commutant is abelian, a pure-program construction already exists with $p=d_c$. The squared dimension is a purification upper bound. Its general optimality is left open by the source.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 21, §5: pure-program upper bound from purification

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

/-- PDF p.21, discussion: purification supplies dc squared, an upper bound
for pure programs. In the abelian case dc already suffices; no general claim
of optimality for pure programs is made. -/
theorem pure_program_upper_bound (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat) (D : TensorIsotypicDecomposition U V) :
    (∃ processor : Superop (I × Fin (compressedDim D ^ 2)) O,
      PureImplements processor (covariantChannels U.mat V.mat) 0) ∧
    (CommutativeMatrixSet (covariantTensorCommutant U.mat V.mat) →
      ∃ processor : Superop (I × Fin (compressedDim D)) O,
        PureImplements processor (covariantChannels U.mat V.mat) 0) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
