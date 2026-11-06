-- Prove2me | Theorems.Thm_SpatialSorting_column_bridges
-- name    : SpatialSorting.column_bridges
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:53:20.030013+00:00
-- url     : https://prove2.me/theorems/4d6c8dcb-79b9-476d-b03a-21fe087b5e4d
-- title:
--   Lemma 7.3 — boundary-rooted column bridges
-- statement:
--   Let $\delta\in(0,1]$ and $\sigma\in\Omega_{D_L}$. For a set $C$ of columns let $\mathcal S_C$ be the set of contours of $\sigma$ whose supports meet $\bigcup_{c\in C}\mathrm{col}_c$, and put $m_C(c)=\sum\{|\overline\gamma|:\gamma\in\Gamma(\sigma)\setminus\mathcal S_C,\ \overline\gamma\cap\mathrm{col}_c\ne\emptyset\}$. Start with $C=\emptyset$; while some column $c\notin C$ has $m_C(c)\ge\delta L$, add the smallest such $c$ to $C$. Let $C^*=C^*(\sigma)$ be the final set, and put $\mathcal S=\mathcal S(\sigma)=\mathcal S_{C^*}$ and $B=B(\sigma)=B_L\cup\bigcup_{c\in C^*}\mathrm{col}_c$. Then:
--
--   1. every unselected contour is admissible in its complementary component; hence $\mathcal S$ is a scaffold and $\sigma\in\Omega^L_{\mathcal S}$;
--   2. $B\supseteq B_L$, and $B$ and $B\cup\overline{\mathcal S}$ are connected;
--   3. $|B|\le|B_L|+\delta^{-1}|\overline{\mathcal S}|\le8L+\delta^{-1}|\overline{\mathcal S}|$;
--   4. fewer than $\delta L^2$ sites $v\in D_L\setminus\overline{\mathcal S}$ have a colour different from the label of their component.
--
--   The construction is deterministic, so $\mathcal S(\sigma)$ is a function of $\sigma$. The selected contours are boundary-rooted witnesses whose number can be counted (Lemma 7.4), while the unselected contours are sparse in every column.
--
--   Differences from the source:
--   - encoding: L, implicitly positive → 1 ≤ L; reason: at L = 0 clause (d) would read 0 < 0, which is false; the hypothesis excludes only the empty rhombus, which the paper never considers
--   - encoding: 'the label of their component' → for every labelling satisfying (W3); reason: the labels of the complementary components of a scaffold are determined by (W3)
--   - encoding: the while-loop of the construction → L iterations of the step 'add the smallest column c ∉ C with m_C(c) ≥ δL, if any'; reason: each effective step adds one of the L columns, so the loop stops within L steps and further steps change nothing
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44)

import Mathlib
import Definitions.Def_SpatialSorting_ReachIn
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_B
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_supp
import Definitions.Def_SpatialSorting_AdmissibleIn
import Definitions.Def_SpatialSorting_comps
import Definitions.Def_SpatialSorting_IsLabeling
import Definitions.Def_SpatialSorting_IsScaffold
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_omegaS
import Definitions.Def_SpatialSorting_bridgeFamily
import Definitions.Def_SpatialSorting_bridgeRoot
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 7.3 — boundary-rooted column bridges.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 7.3, p. 43 (PDF p. 44).

Formalization Notes:
- encoding: L, implicitly positive → 1 ≤ L. At L = 0 clause (d) would read 0 < 0, which is false; the hypothesis excludes only the empty rhombus, which the paper never considers.
- encoding: 'the label of their component' → for every labelling satisfying (W3). The labels of the complementary components of a scaffold are determined by (W3).
- encoding: the while-loop of the construction → L iterations of the step 'add the smallest column c ∉ C with m_C(c) ≥ δL, if any'. Each effective step adds one of the L columns, so the loop stops within L steps and further steps change nothing. -/
theorem column_bridges {q L : ℕ} [NeZero q] (hL : 1 ≤ L) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (σ : Coloring q L) :
    let S := bridgeFamily δ L σ
    let Bσ := bridgeRoot δ L σ
    ((∀ γ ∈ contourSet σ, γ ∉ S → ∃ V ∈ comps L S, γ.support ⊆ V ∧ AdmissibleIn V γ) ∧
      IsScaffold L S ∧ σ ∈ omegaS L S) ∧
    (B L ⊆ Bσ ∧ (∀ x ∈ Bσ, ∀ y ∈ Bσ, ReachIn ↑Bσ x y) ∧
      ∀ x ∈ Bσ ∪ supp S, ∀ y ∈ Bσ ∪ supp S, ReachIn ↑(Bσ ∪ supp S) x y) ∧
    ((Bσ.card : ℝ) ≤ ((B L).card : ℝ) + δ⁻¹ * ((supp S).card : ℝ) ∧
      ((B L).card : ℝ) + δ⁻¹ * ((supp S).card : ℝ) ≤ 8 * (L : ℝ) + δ⁻¹ * ((supp S).card : ℝ)) ∧
    ∀ lab, IsLabeling L S lab →
      ((((D L \ supp S).filter
        (fun v => ∃ V ∈ comps L S, v ∈ V ∧ extendBy 0 (I L) σ v ≠ lab V)).card : ℕ) : ℝ) <
        δ * (L : ℝ) ^ 2 := by sorry

end SpatialSorting
