-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_one_dimensional_multiplicity
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.one_dimensional_multiplicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:16:34.037445+00:00
-- url     : https://prove2.me/theorems/561748c3-37ce-453c-9b86-62cc751314fb
-- title:
--   Proposition 21: one-dimensional tensor irreps occur at most once
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. Assume $U$ is irreducible and $d_2\le d_1$. For every continuous unitary one-dimensional type $\lambda$, let $n_\lambda$ be its actual multiplicity in $\overline U\otimes V$, equivalently the dimension of its simultaneous intertwiner/eigenvector space. Then
--
--   $$n_\lambda\le1.$$
--
--   The multiplicity is zero when the type is absent. No irreducibility of $V$ is assumed. This rules out repeated scalar irreducibles in this dimension regime.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 11, Proposition 21: one-dimensional tensor irreps occur at most once

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

/-- PDF pp.11--12, Proposition 21: no irreducibility of V is required;
the one-dimensional type can have multiplicity zero. -/
theorem one_dimensional_multiplicity (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat)
    (hd : Fintype.card O ≤ Fintype.card I) (lambda : ContinuousUnitaryRep G (Fin 1)) :
    oneDimMultiplicity U V lambda ≤ 1 := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
