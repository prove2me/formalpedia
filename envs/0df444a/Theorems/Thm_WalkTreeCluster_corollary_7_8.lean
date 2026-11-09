-- Prove2me | Theorems.Thm_WalkTreeCluster_corollary_7_8
-- name    : WalkTreeCluster.corollary_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:25.490637+00:00
-- url     : https://prove2.me/theorems/5772df43-c52a-4820-b29f-9475415bed82
-- title:
--   Corollary 7.8: preservation of a cluster mean under an average diagonal loss $\beta$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   Let $C$ be a cluster, $i\ge0$ a stage, and $\beta$ a real with $\frac1{|C|}\sum_{u\in C}(1-D_i(u,u))\le\beta$. Then
--   1. $\displaystyle0\le\frac1{|C|}-\|F_iD_i^{1/2}u_C\|_{F,w}^2\le\frac{48\beta+24\epsilon t}{a|C|}$;
--   2. $\displaystyle\frac{1-(48\beta+24\epsilon t)/a-3\sqrt\beta}{|C|}\le\|F_iu_C\|_{F,w}^2\le\frac{1+9a^{40}}{|C|}$.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Corollary 7.8, p.45

import Mathlib
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Corollary 7.8** (Preservation of a cluster mean), p.45 (PDF p.48). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

For every cluster `C` and stage `i ≥ 0`, if `|C|⁻¹ Σ_{u ∈ C} (1 − D_i(u, u)) ≤ β`, then
(1) `0 ≤ 1/|C| − ‖F_i D_i^{1/2} u_C‖²_{F,w} ≤ (48β + 24ϵt)/(a|C|)`;
(2) `(1 − (48β + 24ϵt)/a − 3√β)/|C| ≤ ‖F_i u_C‖²_{F,w} ≤ (1 + 9a^{40})/|C|`.

**Formalization Note.** "Cluster" means a member of a family of clusters (Definition 1.2) of the
graph for the same `ϵ, ϕ`; `β` is any real (the hypothesis forces `β ≥ 0`); `t` is the integer
walk length of Table 1. Parameter range: `d ≥ 1`, undirected, no parallel edges, `0 < ϕ ≤ 1`,
`ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem corollary_7_8 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (𝒞 : Finset (Finset (Fin n)))
    (h𝒞 : IsClusterFamily nbr ϵ ϕ 𝒞) (C : Finset (Fin n)) (hC : C ∈ 𝒞) (i : ℕ) (β : ℝ)
    (hβ : (1 / (C.card : ℝ)) * ∑ u ∈ C, (1 - Ddiag nbr ϵ ϕ i u u) ≤ β) :
    (0 ≤ 1 / (C.card : ℝ) -
        wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i ((Dsqrt nbr ϵ ϕ i).mulVec (clusterMean C))) ∧
      1 / (C.card : ℝ) -
          wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i ((Dsqrt nbr ϵ ϕ i).mulVec (clusterMean C))) ≤
        (48 * β + 24 * ϵ * tParam ϵ ϕ) / (aParam ϵ ϕ * C.card)) ∧
    ((1 - (48 * β + 24 * ϵ * tParam ϵ ϕ) / aParam ϵ ϕ - 3 * Real.sqrt β) / C.card ≤
        wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i (clusterMean C)) ∧
      wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i (clusterMean C)) ≤
        (1 + 9 * aParam ϵ ϕ ^ 40) / C.card) := by sorry

end WalkTreeCluster
