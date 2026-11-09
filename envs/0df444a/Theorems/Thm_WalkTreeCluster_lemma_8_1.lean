-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_8_1
-- name    : WalkTreeCluster.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:02:03.662812+00:00
-- url     : https://prove2.me/theorems/fb76de7d-44b1-4bf7-8e32-0c9f8c7b68dc
-- title:
--   Lemma 8.1: $|B_{\rm clusters}\cap C|\le2c_{\rm loc}a^{26}|C|$; outside it, norms $(1\pm O(a))/|C|$ and distances $\le20a^8/|C|$ at stage $i_C$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$) and $\mathcal C$ a family of clusters for $\epsilon,\phi$, with the parameters of Table 1, $0<\epsilon\le c_0\phi^2$ and $c_0$ defined from the constant $c_{\rm loc}$ of Lemma 8.3.
--   Let $B_{\rm clusters}\subseteq S$ be the exceptional set of Definition 8.8. Then:
--   1. $|B_{\rm clusters}\cap C|\le2c_{\rm loc}a^{26}|C|$ for every cluster $C$;
--   2. outside $B_{\rm clusters}$ the deviation from the filtered cluster mean is small at every stage:
--   $$\|F_i\mathbb 1_u-F_iu_C\|_{F,w}\le\frac{a^{10}}{\sqrt{\alpha^i}}\qquad(u\in C\setminus B_{\rm clusters},\ i\ge1);$$
--   3. with $i_C=\max\{1,\lfloor\log_\alpha(a^{10}|C|)\rfloor\}$, for all $u,v\in C\setminus B_{\rm clusters}$,
--   $$\|F_{i_C}\mathbb 1_u\|_{F,w}^2=\frac{1\pm O(a)}{|C|},\qquad\|F_{i_C}(\mathbb 1_u-\mathbb 1_v)\|_{F,w}^2\le\frac{20a^8}{|C|}.$$
--   The constant in $O(a)$ is absolute.
--
--   This is the statement that vertices of a cluster outside a small exceptional set look alike at the cluster's scale.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - reading: c_loc is the absolute constant of Lemma 8.3 and c₀ = (1/8)min{10⁻⁴, (128c_loc)^{−1/60}}^{1000} (Table 1) → any c_loc for which the conclusion of Lemma 8.3 holds (LocalVariationConst c_loc), with ϵ ≤ c0Param(c_loc)·ϕ²; reason: Table 1 defines c₀ from the constant of Lemma 8.3; with lemma_8_3 (∃ c_loc) this is the page's statement
--   - reading: 1 ± O(a) → ∃ C₁, chosen before the graph, with (1 − C₁a)/|C| ≤ ‖F_{i_C}1_u‖² ≤ (1 + C₁a)/|C|; reason: the O(·) constant is absolute (proof on p.59)
--   - encoding: a deterministic set B_clusters ⊆ S → the set B_clusters of Definition 8.8, with B_clusters ⊆ S as a conclusion; reason: the proof takes B_clusters from Definition 8.8 (p.58)
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 8.1, p.46; Definition 8.8, p.58

import Mathlib
import Definitions.Def_WalkTreeCluster_ExceptionalSets
import Definitions.Def_WalkTreeCluster_LocalVariationConst

namespace WalkTreeCluster

/-- **Lemma 8.1** (Comparable norms and small distances in `C`), p.46 (PDF p.49), with
`B_clusters` of Definition 8.8, p.58. Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random
Walks in Arbitrary Noise*, STOC 2027 submission (manuscript sha256 638eeef1…).

`B_clusters ⊆ S` satisfies `|B_clusters ∩ C| ≤ 2 c_loc a^{26} |C|` for every cluster `C`. Outside
`B_clusters`, `‖F_i 1_u − F_i u_C‖_{F,w} ≤ a^{10}/√(α^i)` (`u ∈ C ∖ B_clusters`, `i ≥ 1`), Eq. (69).
For `i_C = max{1, ⌊log_α(a^{10}|C|)⌋}` and every `u, v ∈ C ∖ B_clusters`,
`‖F_{i_C} 1_u‖²_{F,w} = (1 ± O(a))/|C|` and `‖F_{i_C}(1_u − 1_v)‖²_{F,w} ≤ 20a⁸/|C|`.

**Formalization Note.** `c_loc` is a constant for which the conclusion of Lemma 8.3 holds
(`LocalVariationConst`; Table 1: "c_loc — absolute constant in Lemma 8.3"), and the parameters
satisfy Table 1 with `c₀ = c0Param c_loc`. "`1 ± O(a)`" is: there is a constant `C₁`, chosen before
the graph, with `(1 − C₁a)/|C| ≤ ‖F_{i_C} 1_u‖²_{F,w} ≤ (1 + C₁a)/|C|`. The deterministic set is
`B_clusters` of Definition 8.8, which the proof uses. -/
theorem lemma_8_1 (cloc : ℝ) (hcloc : LocalVariationConst cloc) :
    ∃ C₁ : ℝ, ∀ (n d : ℕ) (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
      (𝒞 : Finset (Finset (Fin n))),
      1 ≤ d → IsUndirected nbr → NoParallel nbr → 0 < ϕ → ϕ ≤ 1 → 0 < ϵ →
      ϵ ≤ c0Param cloc * ϕ ^ 2 → IsClusterFamily nbr ϵ ϕ 𝒞 →
      Bclusters nbr ϵ ϕ 𝒞 ⊆ clusterUnion 𝒞 ∧
      (∀ C ∈ 𝒞, ((Bclusters nbr ϵ ϕ 𝒞 ∩ C).card : ℝ) ≤ 2 * cloc * aParam ϵ ϕ ^ 26 * C.card) ∧
      (∀ C ∈ 𝒞, ∀ u ∈ C, u ∉ Bclusters nbr ϵ ϕ 𝒞 → ∀ i : ℕ, 1 ≤ i →
        Real.sqrt (wNormSq (aParam ϵ ϕ)
            (filter nbr ϵ ϕ i (coord u) - filter nbr ϵ ϕ i (clusterMean C))) ≤
          aParam ϵ ϕ ^ 10 / Real.sqrt (alphaParam ϵ ϕ ^ i)) ∧
      (∀ C ∈ 𝒞, ∀ u ∈ C, ∀ v ∈ C, u ∉ Bclusters nbr ϵ ϕ 𝒞 → v ∉ Bclusters nbr ϵ ϕ 𝒞 →
        (1 - C₁ * aParam ϵ ϕ) / C.card ≤
          wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ (clusterStage ϵ ϕ C) (coord u)) ∧
        wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ (clusterStage ϵ ϕ C) (coord u)) ≤
          (1 + C₁ * aParam ϵ ϕ) / C.card ∧
        wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ (clusterStage ϵ ϕ C) (coord u - coord v)) ≤
          20 * aParam ϵ ϕ ^ 8 / C.card) := by sorry

end WalkTreeCluster
