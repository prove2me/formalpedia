-- Prove2me | Theorems.Thm_SpatialSorting_gluing_ordinary_fillings
-- name    : SpatialSorting.gluing_ordinary_fillings
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:33.567702+00:00
-- url     : https://prove2.me/theorems/17a52b85-112d-46c6-b293-23fc3329440c
-- title:
--   Lemma 6.4 — gluing ordinary fillings into the full canonical ensemble
-- statement:
--   Let $\mathcal S$ be a scaffold with labels $j_k$, let $V^{(j)}=\bigcup_{k:j_k=j}V_k$ be its label groups (Corollary 3.13), and let $\mathbf n$ be an interior count vector. Let $(m_{i,j})$ be a nonnegative integer table with
--
--   $$\sum_im_{i,j}=|V^{(j)}|,\qquad\sum_jm_{i,j}=n_i+|B_L|\mathbb 1_{i=0}-N_i(\mathcal S).$$
--
--   For each $j$ let $\xi_j:V^{(j)}\to\{0,\dots,q-1\}$ satisfy $\xi_j|_{F(V^{(j)})}\equiv j$ and $\mathbf n(\xi_j)=\mathbf m_{\cdot,j}$, with no contour restriction. Then:
--
--   1. $\sigma=\omega_{\mathcal S}\sqcup\bigsqcup_j\xi_j$ belongs to $\Omega_{D_L,\mathbf n}$ (it vanishes on $B_L$ and has interior counts $\mathbf n$);
--   2. the map $(\xi_j)_j\mapsto\sigma$ is injective;
--   3. if $h_0=0$, then $e^{-\beta H(\sigma)+\mathbf h\cdot\mathbf n}=e^{-\beta\mathcal H(\mathcal S)+\mathbf h\cdot\mathbf N(\mathcal S)}\prod_je^{-\beta H_{V^{(j)}}(\xi_j)+\mathbf h\cdot\mathbf m_{\cdot,j}}$;
--   4. consequently, if $h_0=0$,
--   $$Z^{\rm tot}_{\mathbf n}(\beta,\mathbf h)\ge e^{-\beta\mathcal H(\mathcal S)+\mathbf h\cdot\mathbf N(\mathcal S)}\prod_{j=0}^{q-1}\mathcal Z_{j,\mathbf m_{\cdot,j}}(V^{(j)}),\tag{34}$$
--   with $\mathcal Z$ evaluated at the same field;
--   5. for a general field $\mathbf h$ the right side of (34) acquires the factor $e^{-h_0|B_L|}$.
--
--   The lemma lets the lower bound use ordinary fillings, which carry no contour restriction, so that the switching estimate of Lemma 6.2 applies.
--
--   Differences from the source:
--   - encoding: Σ_j m_{i,j} = n_i + |B_L|1_{i=0} − N_i(𝒮) → Σ_j m_{i,j} + N_i(𝒮) = n_i + |B_L|1_{i=0}; reason: the same equation between nonnegative integers, without natural-number subtraction
--   - encoding: σ ∈ Ω_{D_L,n}; the map (ξ_j)_j ↦ σ is injective → σ (a colouring of ℤ², equal to ω_𝒮 off the label groups) vanishes on B_L and has interior counts n; two admissible tuples whose glued colourings agree on D_L are equal; reason: Ω_{D_L,n} consists of the colourings of D_L wired to 0 on B_L with interior counts n
--   - encoding: the labels j_k of the complementary components → every labelling lab : Finset (ℤ × ℤ) → Fin q satisfying (W3) and j_0 = 0 (IsLabeling L 𝒮 lab); reason: the labels of the complementary components of a scaffold are determined by (W3), so every such labelling gives the page's labels
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.4, p. 36 (PDF p. 37)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_B
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_cost
import Definitions.Def_SpatialSorting_ordinary
import Definitions.Def_SpatialSorting_ZordFix
import Definitions.Def_SpatialSorting_IsLabeling
import Definitions.Def_SpatialSorting_IsScaffold
import Definitions.Def_SpatialSorting_Ztot
import Definitions.Def_SpatialSorting_Ncount
import Definitions.Def_SpatialSorting_labelGroup
import Definitions.Def_SpatialSorting_glueFillings
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 6.4 — gluing ordinary fillings into the full canonical ensemble.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 6.4, p. 36 (PDF p. 37).

Formalization Notes:
- encoding: Σ_j m_{i,j} = n_i + |B_L|1_{i=0} − N_i(𝒮) → Σ_j m_{i,j} + N_i(𝒮) = n_i + |B_L|1_{i=0}. The same equation between nonnegative integers, without natural-number subtraction.
- encoding: σ ∈ Ω_{D_L,n}; the map (ξ_j)_j ↦ σ is injective → σ (a colouring of ℤ², equal to ω_𝒮 off the label groups) vanishes on B_L and has interior counts n; two admissible tuples whose glued colourings agree on D_L are equal. Ω_{D_L,n} consists of the colourings of D_L wired to 0 on B_L with interior counts n.
- encoding: the labels j_k of the complementary components → every labelling lab : Finset (ℤ × ℤ) → Fin q satisfying (W3) and j_0 = 0 (IsLabeling L 𝒮 lab). The labels of the complementary components of a scaffold are determined by (W3), so every such labelling gives the page's labels. -/
theorem gluing_ordinary_fillings {q L : ℕ} [NeZero q]
    (A : Matrix (Fin q) (Fin q) ℝ) (hA : IsCostMatrix A) (β : ℝ)
    (S : Finset (Contour q)) (hS : IsScaffold L S) (lab : Finset (ℤ × ℤ) → Fin q)
    (hlab : IsLabeling L S lab) (n : Fin q → ℕ) (m : Fin q → Fin q → ℕ)
    (hcol : ∀ j, ∑ i, m i j = (labelGroup L S lab j).card)
    (hrow : ∀ i, ∑ j, m i j + Ncount S i = n i + (if i = 0 then (B L).card else 0)) :
    let Adm : ((j : Fin q) → ({v // v ∈ labelGroup L S lab j} → Fin q)) → Prop := fun ξ =>
      ∀ j, ξ j ∈ ordinary j (labelGroup L S lab j) ∧
        ∀ i, nV (labelGroup L S lab j) (extendBy j _ (ξ j)) i = m i j
    let RHS : (Fin q → ℝ) → ℝ := fun h =>
      Real.exp (-β * ∑ γ ∈ S, cost A γ + ∑ i, h i * (Ncount S i : ℝ)) *
        ∏ j : Fin q, ZordFix A β h j (labelGroup L S lab j) (fun i => m i j)
    (∀ ξ, Adm ξ →
      (∀ v ∈ B L, glueFillings L S lab ξ v = 0) ∧
      (∀ i, nV (I L) (glueFillings L S lab ξ) i = n i) ∧
      ∀ h : Fin q → ℝ, h 0 = 0 →
        Real.exp (-β * HV A (D L) (glueFillings L S lab ξ) + ∑ i, h i * (n i : ℝ)) =
          Real.exp (-β * ∑ γ ∈ S, cost A γ + ∑ i, h i * (Ncount S i : ℝ)) *
            ∏ j : Fin q, Real.exp (-β * HV A (labelGroup L S lab j) (extendBy j _ (ξ j)) +
              ∑ i, h i * (m i j : ℝ))) ∧
    (∀ ξ ξ', Adm ξ → Adm ξ' →
      (∀ v ∈ D L, glueFillings L S lab ξ v = glueFillings L S lab ξ' v) → ξ = ξ') ∧
    (∀ h : Fin q → ℝ, h 0 = 0 → RHS h ≤ Ztot A β h L n) ∧
    ∀ h : Fin q → ℝ, Real.exp (-(h 0) * ((B L).card : ℝ)) * RHS h ≤ Ztot A β h L n := by sorry

end SpatialSorting
