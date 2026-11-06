-- Prove2me | Theorems.Thm_SpatialSorting_scaffold_factorization
-- name    : SpatialSorting.scaffold_factorization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:56.24747+00:00
-- url     : https://prove2.me/theorems/d636bbe9-bc36-4484-aee3-d33b5af27ffa
-- title:
--   Lemma 3.11 — physical scaffold factorization
-- statement:
--   Let $\mathcal S$ be a scaffold with complementary components $V_k$ and labels $j_k$. Define
--
--   $$\Phi_{\mathcal S}(\sigma)=(\sigma|_{V_k})_k,\qquad \Psi_{\mathcal S}((\tau_k)_k)=\sigma\ \text{ with }\ \sigma|_{\overline{\mathcal S}}=\omega_{\mathcal S},\ \sigma|_{V_k}=\tau_k .$$
--
--   Then:
--
--   1. $\Phi_{\mathcal S}$ is a bijection $\Omega^L_{\mathcal S}\to\prod_k\Omega^L_{j_k}(V_k)$ with inverse $\Psi_{\mathcal S}$, where $\Omega^L_j(V)$ is the restricted ensemble of Definition 3.5.
--   2. For $\sigma=\Psi_{\mathcal S}((\tau_k)_k)$,
--   $$H(\sigma)=\mathcal H(\mathcal S)+\sum_kH_{V_k}(\tau_k),\qquad \mathbf n_{D_L}(\sigma)=\mathbf N(\mathcal S)+\sum_k\mathbf n(\tau_k),\tag{14}$$
--   $$\Gamma(\sigma)=\mathcal S\ \sqcup\ \bigsqcup_k\Gamma_{V_k}(\tau_k)\quad\text{(as assigned contours).}\tag{15}$$
--   3. For every field $\mathbf h$ and every family of count vectors $(\mathbf m^{(k)})_k$,
--   $$\sum_{\sigma\in\Omega^L_{\mathcal S},\ \mathbf n(\sigma|_{V_k})=\mathbf m^{(k)}\ \forall k}W_{\mathbf h}(\sigma)=e^{-\beta\mathcal H(\mathcal S)+\mathbf h\cdot\mathbf N(\mathcal S)}\prod_kZ^L_{j_k,\mathbf m^{(k)}}(\beta,\mathbf h,V_k).\tag{16}$$
--   4. Summing over $(\mathbf m^{(k)})_k$,
--   $$Z^L_{\mathcal S}(\beta,\mathbf h)=\exp\Bigl[-\beta\mathcal H(\mathcal S)+\sum_ih_iN_i(\mathcal S)\Bigr]\prod_kZ^L_{j_k}(\beta,\mathbf h,V_k),\tag{17}$$
--   where the product includes the component $V_0$ touching the wired boundary, with label $0$, and $N_i(\mathcal S)$ counts the scaffold sites, including sites of $B_L$ on its support.
--
--   The factorization reduces a contour-restricted partition function of the whole rhombus to independent regional ensembles, and is the exact identity behind both strands of the proof.
--
--   **Formalization Note** The product $\prod_k\Omega^L_{j_k}(V_k)$ is the set of dependent functions on the components; $\Gamma_{V_k}(\tau_k)$ is computed from the extension of $\tau_k$ by $j_k$ (p.19).
--
--   Differences from the source:
--   - encoding: Φ_𝒮 is a bijection with inverse Ψ_𝒮 → Φ maps Ω^L_𝒮 into the product, Ψ maps the product into Ω^L_𝒮, and they are inverse on these sets; reason: the same statement
--   - encoding: disjoint union ⊔ in (15) → an equality of sets together with the disjointness of 𝒮 from the regional contours and of the regional contour sets of distinct components; reason: the same statement
--   - encoding: a family of count vectors (m^(k))_k indexed by the components → a function m from finite sets of sites to count vectors, read on the components; reason: only its values on the components enter
--   - encoding: the labels j_k of the complementary components → every labelling lab : Finset (ℤ × ℤ) → Fin q satisfying (W3) and j_0 = 0 (IsLabeling L 𝒮 lab); reason: the labels of the complementary components of a scaffold are determined by (W3), so every such labelling gives the page's labels
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.11, p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_SpatialSorting_D
import Definitions.Def_SpatialSorting_I
import Definitions.Def_SpatialSorting_IsCostMatrix
import Definitions.Def_SpatialSorting_Coloring
import Definitions.Def_SpatialSorting_extendBy
import Definitions.Def_SpatialSorting_HV
import Definitions.Def_SpatialSorting_nV
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_contoursOn
import Definitions.Def_SpatialSorting_cost
import Definitions.Def_SpatialSorting_nbhd
import Definitions.Def_SpatialSorting_restricted
import Definitions.Def_SpatialSorting_Zres
import Definitions.Def_SpatialSorting_ZresFix
import Definitions.Def_SpatialSorting_comps
import Definitions.Def_SpatialSorting_IsLabeling
import Definitions.Def_SpatialSorting_IsScaffold
import Definitions.Def_SpatialSorting_contourSet
import Definitions.Def_SpatialSorting_omegaS
import Definitions.Def_SpatialSorting_Wt
import Definitions.Def_SpatialSorting_ZS
import Definitions.Def_SpatialSorting_Ncount
import Definitions.Def_SpatialSorting_glueScaffold
open Classical Filter Topology

namespace SpatialSorting

/-- Lemma 3.11 — physical scaffold factorization.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), Lemma 3.11, p. 21 (PDF p. 22).

Formalization Notes:
- encoding: Φ_𝒮 is a bijection with inverse Ψ_𝒮 → Φ maps Ω^L_𝒮 into the product, Ψ maps the product into Ω^L_𝒮, and they are inverse on these sets. The same statement.
- encoding: disjoint union ⊔ in (15) → an equality of sets together with the disjointness of 𝒮 from the regional contours and of the regional contour sets of distinct components. The same statement.
- encoding: a family of count vectors (m^(k))_k indexed by the components → a function m from finite sets of sites to count vectors, read on the components. Only its values on the components enter.
- encoding: the labels j_k of the complementary components → every labelling lab : Finset (ℤ × ℤ) → Fin q satisfying (W3) and j_0 = 0 (IsLabeling L 𝒮 lab). The labels of the complementary components of a scaffold are determined by (W3), so every such labelling gives the page's labels. -/
theorem scaffold_factorization {q L : ℕ} [NeZero q]
    (A : Matrix (Fin q) (Fin q) ℝ) (hA : IsCostMatrix A) (β : ℝ)
    (S : Finset (Contour q)) (hS : IsScaffold L S) (lab : Finset (ℤ × ℤ) → Fin q)
    (hlab : IsLabeling L S lab) :
    let Φ : Coloring q L → (V : {V // V ∈ comps L S}) → ({v // v ∈ V.1} → Fin q) :=
      fun σ V v => extendBy 0 (I L) σ v.1
    let P : Set ((V : {V // V ∈ comps L S}) → ({v // v ∈ V.1} → Fin q)) :=
      {τ | ∀ V, τ V ∈ restricted (lab V.1) V.1}
    (Set.MapsTo Φ ↑(omegaS L S) P ∧ Set.MapsTo (glueScaffold S) P ↑(omegaS L S) ∧
      Set.InvOn (glueScaffold S) Φ ↑(omegaS L S) P) ∧
    (∀ τ ∈ P,
      HV A (D L) (extendBy 0 (I L) (glueScaffold S τ)) =
          ∑ γ ∈ S, cost A γ + ∑ V : {V // V ∈ comps L S}, HV A V.1 (extendBy (lab V.1) V.1 (τ V)) ∧
      (∀ i, nV (D L) (extendBy 0 (I L) (glueScaffold S τ)) i =
          Ncount S i + ∑ V : {V // V ∈ comps L S}, nV V.1 (extendBy (lab V.1) V.1 (τ V)) i) ∧
      contourSet (glueScaffold S τ) =
          S ∪ Finset.univ.biUnion (fun V : {V // V ∈ comps L S} =>
            contoursOn (nbhd V.1) (extendBy (lab V.1) V.1 (τ V))) ∧
      Disjoint S (Finset.univ.biUnion (fun V : {V // V ∈ comps L S} =>
            contoursOn (nbhd V.1) (extendBy (lab V.1) V.1 (τ V)))) ∧
      ∀ V V' : {V // V ∈ comps L S}, V ≠ V' →
        Disjoint (contoursOn (nbhd V.1) (extendBy (lab V.1) V.1 (τ V)))
          (contoursOn (nbhd V'.1) (extendBy (lab V'.1) V'.1 (τ V')))) ∧
    (∀ (h : Fin q → ℝ) (m : Finset (ℤ × ℤ) → Fin q → ℕ),
      ∑ σ ∈ (omegaS L S).filter
          (fun σ => ∀ V ∈ comps L S, ∀ i, nV V (extendBy 0 (I L) σ) i = m V i), Wt A β h σ =
        Real.exp (-β * ∑ γ ∈ S, cost A γ + ∑ i, h i * (Ncount S i : ℝ)) *
          ∏ V ∈ comps L S, ZresFix A β h (lab V) V (m V)) ∧
    ∀ h : Fin q → ℝ,
      ZS A β h L S = Real.exp (-β * ∑ γ ∈ S, cost A γ + ∑ i, h i * (Ncount S i : ℝ)) *
        ∏ V ∈ comps L S, Zres A β h (lab V) V := by sorry

end SpatialSorting
