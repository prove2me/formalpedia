-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_compact_induced
-- name    : QAlgorithms.Papers.Independent.Support21.P20.compact_induced
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T05:02:24.90317+00:00
-- url     : https://prove2.me/theorems/150a8479-d631-4d42-a9d3-d7bb2da5fb51
-- title:
--   Compactness passes to every measurable induced subspace
-- statement:
--   Let $(X,\mathcal M,\mathcal N)$ be a compact enhanced measurable space. Thus a compact class $\mathcal K\subseteq\mathcal M$ has the finite-intersection property implication and every nonnegligible measurable set contains a nonnegligible member of $\mathcal K$. For every $m\in\mathcal M$,
--
--   $$(m,\mathcal M_m,\mathcal N_m)\text{ is compact}.$$
--
--   Here $\mathcal M_m$ and $\mathcal N_m$ consist of the measurable and negligible ambient subsets contained in $m$. No nonemptiness, nonnegligibility, topology, or localizability of $m$ is assumed. **Formalization Note** Subsets of the induced space are represented by ambient subsets contained in $m$; all intersections in its compact-class definition are relative to $m$.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 37, Lemma 4.61

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 4.61, PDF p.37: no nonemptiness or nonnegligibility of m is required. -/
theorem compact_induced (X : Type u) (E : Enhanced X)
    (hE : IsCompactEnhancedOn E Set.univ) (m : Set X) (hm : m ∈ E.measurable) :
    IsCompactEnhancedOn E m := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
