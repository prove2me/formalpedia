-- Prove2me | Theorems.Thm_SpatialSorting_closed_selections_are_scaffolds
-- name    : SpatialSorting.closed_selections_are_scaffolds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:17.882632+00:00
-- url     : https://prove2.me/theorems/3a64e4dc-8bce-4f34-b8f6-c59ff4e31310
-- title:
--   Lemma 3.10 — closed selections are scaffolds
-- statement:
--   Let $\sigma\in\Omega_{D_L}$ and $\mathcal S\subseteq\Gamma(\sigma)$, and suppose every $\gamma\in\Gamma(\sigma)\setminus\mathcal S$ is admissible in the complementary component $V_k$ of $D_L\setminus\overline{\mathcal S}$ containing it. Then $\mathcal S$ is a scaffold. More precisely, there are labels $j_k$ as in (W3), with $j_0=0$, such that for each $k$ the set
--
--   $$W_k=V_k\setminus\bigcup\bigl\{F_\gamma:\ \gamma\in\Gamma(\sigma)\setminus\mathcal S,\ \overline\gamma\subseteq V_k\bigr\}$$
--
--   is connected, contains every site of $V_k$ adjacent to $V_k^c$, consists of correct sites, and $\sigma\equiv j_k$ on $W_k$.
--
--   This shows that conditions (W2) and (W3) hold automatically for every selection of contours of a configuration that is closed under planar admissibility, in particular for the optimal contour set and for the bridge selections of Lemma 7.3.
--
--   Differences from the source:
--   - encoding: 'admissible in the component V_k containing it' → there is a complementary component V containing its support in which it is admissible; reason: an unselected contour is connected and disjoint from 𝒮̄, so it lies in a unique component (p.20)
--   - encoding: 'where j_k is the label in (W3), and j_0 = 0' → there is a labelling satisfying (W3) and j_0 = 0 for which the clauses hold; reason: the label of a component adjacent to 𝒮̄ or meeting L_0 is determined by (W3); the clauses fix it on every component
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.10, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_SpatialSorting_tri
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_bad
import Definitions.Def_SpatialSorting_filled
import Definitions.Def_SpatialSorting_AdmissibleIn
import Definitions.Def_SpatialSorting_comps
import Definitions.Def_SpatialSorting_IsLabeling
import Definitions.Def_SpatialSorting_IsScaffold
import Definitions.Def_SpatialSorting_contourSet
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 3.10 — closed selections are scaffolds.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.10, p. 21 (PDF p. 22).

Formalization Notes:
- encoding: 'admissible in the component V_k containing it' → there is a complementary component V containing its support in which it is admissible. An unselected contour is connected and disjoint from 𝒮̄, so it lies in a unique component (p.20).
- encoding: 'where j_k is the label in (W3), and j_0 = 0' → there is a labelling satisfying (W3) and j_0 = 0 for which the clauses hold. The label of a component adjacent to 𝒮̄ or meeting L_0 is determined by (W3); the clauses fix it on every component. -/
theorem closed_selections_are_scaffolds {q L : ℕ} [NeZero q]
    (σ : Coloring q L) (S : Finset (Contour q)) (hS : S ⊆ contourSet σ)
    (hadm : ∀ γ ∈ contourSet σ, γ ∉ S →
      ∃ V ∈ comps L S, γ.support ⊆ V ∧ AdmissibleIn V γ) :
    IsScaffold L S ∧ ∃ lab, IsLabeling L S lab ∧ ∀ V ∈ comps L S,
      let W := V \ ((contourSet σ \ S).filter (fun γ => γ.support ⊆ V)).biUnion filled
      (∀ x ∈ W, ∀ y ∈ W, ReachIn ↑W x y) ∧
      (∀ v ∈ V, (∃ u, u ∉ V ∧ tri.Adj v u) → v ∈ W) ∧
      (∀ v ∈ W, v ∉ bad (extendBy 0 (I L) σ)) ∧
      (∀ v ∈ W, extendBy 0 (I L) σ v = lab V) := by sorry

end SpatialSorting
