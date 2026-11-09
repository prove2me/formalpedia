-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_8_7
-- name    : WalkTreeCluster.lemma_8_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:02:19.134807+00:00
-- url     : https://prove2.me/theorems/848217bc-b6d9-40e9-9741-414c1f517ff5
-- title:
--   Lemma 8.7: retention $k_i(C)>1-a^2$ and cluster-mean norms in $[(1-100a)/|C|,(1+9a^{40})/|C|]$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$) and $\mathcal C$ a family of clusters for $\epsilon,\phi$, with the parameters of Table 1, $0<\epsilon\le c_0\phi^2$ and $c_0$ defined from the constant $c_{\rm loc}$ of Lemma 8.3.
--   Fix a cluster $C$ and a stage $i\ge0$.
--   1. (Retention) If $\alpha^i\le a^{10}|C|$, then
--   $$\frac1{|C|}\sum_{u\in C}\big(1-\mathbb E[\mathrm{Keep}_u(i)^2]\big)<a^2,\qquad k_i(C)>1-a^2 .$$
--   2. (Cluster mean) If $i\le1$ or $\alpha^i\le a^{10}|C|$, then
--   $$\frac{1-100a}{|C|}\le\|F_iu_C\|_{F,w}^2\le\frac{1+9a^{40}}{|C|}.$$
--
--   Keep scores do not erase a cluster before its size scale.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - reading: c_loc is the absolute constant of Lemma 8.3 and c₀ = (1/8)min{10⁻⁴, (128c_loc)^{−1/60}}^{1000} (Table 1) → any c_loc for which the conclusion of Lemma 8.3 holds (LocalVariationConst c_loc), with ϵ ≤ c0Param(c_loc)·ϕ²; reason: Table 1 defines c₀ from the constant of Lemma 8.3; with lemma_8_3 (∃ c_loc) this is the page's statement
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 8.7, p.56

import Mathlib
import Definitions.Def_WalkTreeCluster_ExceptionalSets
import Definitions.Def_WalkTreeCluster_LocalVariationConst

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 8.7** (No premature loss on a cluster), p.56 (PDF p.59). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

Fix a cluster `C` and a stage `i ≥ 0`, with the parameters in Table 1.
(1) If `α^i ≤ a^{10}|C|`, then `|C|⁻¹ Σ_{u ∈ C} (1 − E[Keep_u(i)²]) < a²` and `k_i(C) > 1 − a²`.
(2) If `i ≤ 1` or `α^i ≤ a^{10}|C|`, then `(1 − 100a)/|C| ≤ ‖F_i u_C‖²_{F,w} ≤ (1 + 9a^{40})/|C|`.

**Formalization Note.** `c_loc` is a constant for which the conclusion of Lemma 8.3 holds
(`LocalVariationConst`), and the parameters satisfy Table 1 with `c₀ = c0Param c_loc`:
`d ≥ 1`, undirected, no parallel edges, `0 < ϕ ≤ 1`, `0 < ϵ ≤ c₀ϕ²`. `E[Keep_u(i)²]` is the second
moment of `keepLaw i u`; `k_i(C)` is Definition 8.2. -/
theorem lemma_8_7 (cloc : ℝ) (hcloc : LocalVariationConst cloc) {n d : ℕ}
    (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d) (hU : IsUndirected nbr)
    (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (hϵc : ϵ ≤ c0Param cloc * ϕ ^ 2) (𝒞 : Finset (Finset (Fin n)))
    (h𝒞 : IsClusterFamily nbr ϵ ϕ 𝒞) (C : Finset (Fin n)) (hC : C ∈ 𝒞) (i : ℕ) :
    (alphaParam ϵ ϕ ^ i ≤ aParam ϵ ϕ ^ 10 * C.card →
      (1 / (C.card : ℝ)) * ∑ u ∈ C, (1 - ∫ x, x ^ 2 ∂(keepLaw nbr ϵ ϕ i u)) < aParam ϵ ϕ ^ 2 ∧
      1 - aParam ϵ ϕ ^ 2 < keepAvg nbr ϵ ϕ i C) ∧
    ((i ≤ 1 ∨ alphaParam ϵ ϕ ^ i ≤ aParam ϵ ϕ ^ 10 * C.card) →
      (1 - 100 * aParam ϵ ϕ) / C.card ≤ wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i (clusterMean C)) ∧
      wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i (clusterMean C)) ≤
        (1 + 9 * aParam ϵ ϕ ^ 40) / C.card) := by sorry

end WalkTreeCluster
