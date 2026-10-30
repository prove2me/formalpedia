-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_covariant_channel_net
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.covariant_channel_net
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:22:21.985012+00:00
-- url     : https://prove2.me/theorems/84872a85-676c-462a-a7e9-1423a1738910
-- title:
--   Proposition 28: finite nets of covariant channels
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. For every $0<\varepsilon<1$, there is a finite set $S\subseteq\mathcal T_{UV}$ such that every target channel $T\in\mathcal T_{UV}$ has an $S_T\in S$ satisfying
--
--   $$\|T-S_T\|_\diamond\le2\varepsilon,\qquad |S|\le(1+2/\varepsilon)^{d_n}.$$
--
--   Neither input nor output irreducibility is assumed. The centers are themselves channels, and the distance uses the full diamond norm. This supplies a finite discretization of the entire covariant class.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 17, Proposition 28: finite nets of covariant channels

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

/-- PDF p.17, Proposition 28: channel centers, full diamond radius 2 epsilon,
and exponent sum nk squared. U and V may both be reducible. -/
theorem covariant_channel_net (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (D : TensorIsotypicDecomposition U V)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ centers : Finset (Superop I O),
      (∀ T ∈ centers, T ∈ covariantChannels U.mat V.mat) ∧
      (∀ T ∈ covariantChannels U.mat V.mat, ∃ S ∈ centers,
        diamond (fun A => T A - S A) ≤ 2 * epsilon) ∧
      (centers.card : ℝ) ≤ (1 + 2 / epsilon) ^ netDim D := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
