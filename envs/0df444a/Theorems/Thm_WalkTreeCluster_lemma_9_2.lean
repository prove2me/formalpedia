-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_9_2
-- name    : WalkTreeCluster.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:52:55.130204+00:00
-- url     : https://prove2.me/theorems/6afb6757-af6b-49a8-b848-66ca19568edb
-- title:
--   Lemma 9.2: ComputeCorrelation misses by more than $a^{20}/(2\alpha^i)$ with probability $\le1/(4(300(h+1))^2)$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   For all $u,v\in V$ and $1\le i\le h$, the output $\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_{w,h}$ of the uncapped call ComputeCorrelation$(u,v,i,h)$ (Algorithm 6) satisfies
--   $$\Pr\Big(\big|\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_{w,h}-\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_w\big|>\frac{a^{20}}{2\alpha^i}\Big)\le\frac{1}{4(300(h+1))^2}.$$
--
--   This is the accuracy of one estimate; a union bound over a trial gives Lemma 9.3.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: Pr(event) → the measure of the set of samples on which the estimate misses, under their joint law (an outer measure if the set is not measurable); reason: an upper bound on the outer measure is the page's bound and never weaker
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 9.2, p.60; Algorithm 6, p.61

import Mathlib
import Definitions.Def_WalkTreeCluster_Filter
import Definitions.Def_WalkTreeCluster_ComputeCorrelation

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 9.2** (Accuracy of ComputeCorrelation), p.60 (PDF p.63). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

For every `u, v ∈ V` and `1 ≤ i ≤ h`, the output `⟨F_i 1_u, F_i 1_v⟩_{w,h}` of the uncapped call
`ComputeCorrelation(u, v, i, h)` (Algorithm 6) satisfies
`Pr(|⟨F_i 1_u, F_i 1_v⟩_{w,h} − ⟨F_i 1_u, F_i 1_v⟩_w| > a^{20}/(2α^i)) ≤ 1/(4(300(h + 1))²)`.

**Formalization Note.** The probability is the measure, under the joint law of the call's samples,
of the set of samples on which the estimate misses; for a non-measurable set this is its outer
measure, so the bound is never weakened. Parameter range: `d ≥ 1`, undirected, no parallel edges,
`0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem lemma_9_2 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (u v : Fin n) (i h : ℕ) (hi : 1 ≤ i) (hih : i ≤ h) :
    corrSampleLaw nbr ϵ ϕ u v i h
        {S | aParam ϵ ϕ ^ 20 / (2 * alphaParam ϵ ϕ ^ i) <
          |corrEstimate ϵ ϕ h S -
            wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u)) (filter nbr ϵ ϕ i (coord v))|} ≤
      ENNReal.ofReal (1 / (4 * (300 * ((h : ℝ) + 1)) ^ 2)) := by sorry

end WalkTreeCluster
