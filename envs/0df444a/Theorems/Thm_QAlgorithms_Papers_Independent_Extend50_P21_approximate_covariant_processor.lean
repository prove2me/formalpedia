-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_approximate_covariant_processor
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.approximate_covariant_processor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:23:02.428225+00:00
-- url     : https://prove2.me/theorems/bf733232-b4e2-48f2-95c8-e1f1538631a4
-- title:
--   Proposition 29: approximate processor for arbitrary representations
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. For arbitrary $U,V$ and every $0<\varepsilon<1$, there is a fixed $\varepsilon$-processor for the entire class $\mathcal T_{UV}$ with
--
--   $$0<p\le(1+2/\varepsilon)^{d_n}.$$
--
--   The error is half the diamond norm. Input irreducibility is unnecessary, so this result applies beyond the exact irreducible-input construction.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 17, Proposition 29: approximate processor for arbitrary representations

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

/-- PDF p.17, Proposition 29: arbitrary representations and half-diamond error. -/
theorem approximate_covariant_processor (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (D : TensorIsotypicDecomposition U V)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ p : ℕ, 0 < p ∧ (p : ℝ) ≤ (1 + 2 / epsilon) ^ netDim D ∧
      ∃ processor : Superop (I × Fin p) O,
        ProgramsChannelClass processor (covariantChannels U.mat V.mat) epsilon := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
