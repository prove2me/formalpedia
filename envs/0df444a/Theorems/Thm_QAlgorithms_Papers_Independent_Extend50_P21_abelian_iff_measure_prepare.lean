-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_abelian_iff_measure_prepare
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.abelian_iff_measure_prepare
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:14:55.609023+00:00
-- url     : https://prove2.me/theorems/3275721d-98b0-4011-9254-3a45df611dcc
-- title:
--   Corollary 19: measure-and-prepare characterization and dimension bound
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. If $U$ is irreducible and $\mathcal K$ is the actual tensor commutant, then
--
--   $$\mathcal K\text{ is abelian}\ \Longleftrightarrow\ \text{there is an exact measure-and-prepare processor for }\mathcal T_{UV}\text{ with }0<p\le K.$$
--
--   The integer $K$ counts distinct occurring irreducible types. This characterizes measure-and-prepare processors, without excluding other finite processors for a nonabelian commutant.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 10, Corollary 19: measure-and-prepare characterization and dimension bound

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

/-- PDF p.10, Corollary 19: both directions, and K counts distinct types. -/
theorem abelian_iff_measure_prepare (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat) (D : TensorIsotypicDecomposition U V) :
    CommutativeMatrixSet (covariantTensorCommutant U.mat V.mat) ↔
      ∃ p : ℕ, 0 < p ∧ p ≤ D.count ∧ ∃ processor : Superop (I × Fin p) O,
        ProgramsChannelClass processor (covariantChannels U.mat V.mat) 0 ∧
        FiniteMeasurePrepareProcessor processor (covariantChannels U.mat V.mat) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
