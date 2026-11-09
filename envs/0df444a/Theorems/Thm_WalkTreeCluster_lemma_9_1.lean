-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_9_1
-- name    : WalkTreeCluster.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:56:58.71644+00:00
-- url     : https://prove2.me/theorems/6008add0-77ab-4811-b418-83fda7609fa8
-- title:
--   Lemma 9.1: $|\langle F_iu_C,F_iu_D\rangle_w|\le101a/\sqrt{|C||D|}$ and the separation (118)
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$) and $\mathcal C$ a family of clusters for $\epsilon,\phi$, with the parameters of Table 1, $0<\epsilon\le c_0\phi^2$ and $c_0$ defined from the constant $c_{\rm loc}$ of Lemma 8.3.
--   Let $C\ne D$ be clusters and let $i\ge1$ satisfy $i=1$ or $\alpha^i\le a^{10}\min\{|C|,|D|\}$. Then
--   $$|\langle F_iu_C,F_iu_D\rangle_w|\le\frac{101a}{\sqrt{|C||D|}}\qquad(117)$$
--   and
--   $$\|F_iu_C-F_iu_D\|_{F,w}^2\ge(1-202a)\Big(\frac1{|C|}+\frac1{|D|}\Big).\qquad(118)$$
--
--   The cluster means are nearly orthogonal under the filter, which is what separates different clusters in the pair test.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - reading: c_loc is the absolute constant of Lemma 8.3 and c₀ = (1/8)min{10⁻⁴, (128c_loc)^{−1/60}}^{1000} (Table 1) → any c_loc for which the conclusion of Lemma 8.3 holds (LocalVariationConst c_loc), with ϵ ≤ c0Param(c_loc)·ϕ²; reason: Table 1 defines c₀ from the constant of Lemma 8.3; with lemma_8_3 (∃ c_loc) this is the page's statement
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 9.1, p.59

import Mathlib
import Definitions.Def_WalkTreeCluster_LocalVariationConst

namespace WalkTreeCluster

/-- **Lemma 9.1** (Near orthogonality of cluster means), p.59 (PDF p.62). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

Let `C, D` be distinct clusters, and let `i ≥ 1` satisfy either `i = 1` or
`α^i ≤ a^{10} min{|C|, |D|}`. Then `|⟨F_i u_C, F_i u_D⟩_w| ≤ 101a/√(|C||D|)` (117), and
`‖F_i u_C − F_i u_D‖²_{F,w} ≥ (1 − 202a)(1/|C| + 1/|D|)` (118).

**Formalization Note.** `c_loc` is a constant for which the conclusion of Lemma 8.3 holds, and the
parameters satisfy Table 1 with `c₀ = c0Param c_loc`: `d ≥ 1`, undirected, no parallel edges,
`0 < ϕ ≤ 1`, `0 < ϵ ≤ c₀ϕ²`. -/
theorem lemma_9_1 (cloc : ℝ) (hcloc : LocalVariationConst cloc) {n d : ℕ}
    (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d) (hU : IsUndirected nbr)
    (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (hϵc : ϵ ≤ c0Param cloc * ϕ ^ 2) (𝒞 : Finset (Finset (Fin n)))
    (h𝒞 : IsClusterFamily nbr ϵ ϕ 𝒞) (C D : Finset (Fin n)) (hC : C ∈ 𝒞) (hD : D ∈ 𝒞)
    (hCD : C ≠ D) (i : ℕ) (hi : 1 ≤ i)
    (hscale : i = 1 ∨ alphaParam ϵ ϕ ^ i ≤ aParam ϵ ϕ ^ 10 * (min C.card D.card : ℕ)) :
    |wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (clusterMean C)) (filter nbr ϵ ϕ i (clusterMean D))| ≤
      101 * aParam ϵ ϕ / Real.sqrt ((C.card : ℝ) * D.card) ∧
    (1 - 202 * aParam ϵ ϕ) * (1 / (C.card : ℝ) + 1 / (D.card : ℝ)) ≤
      wNormSq (aParam ϵ ϕ)
        (filter nbr ϵ ϕ i (clusterMean C) - filter nbr ϵ ϕ i (clusterMean D)) := by sorry

end WalkTreeCluster
