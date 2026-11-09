-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_6_4
-- name    : WalkTreeCluster.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:18.20152+00:00
-- url     : https://prove2.me/theorems/5bbc2519-9096-4986-bf8a-1ee25c80e550
-- title:
--   Lemma 6.4: $\mathbb EX_{u,i}=F_i\mathbb 1_u$ and $\mathbb EX^{\rm keep}_{u,i}=(1-\delta)^{-1}F_iD_{i+1}\mathbb 1_u$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   For every vertex $u$ and stage $i\ge0$,
--   1. $\mathbb E\,X_{u,i}=F_i\mathbb 1_u$;
--   2. $\mathbb E\,X^{\rm keep}_{u,i}=\frac1{1-\delta}F_iD_{i+1}\mathbb 1_u$.
--
--   The walk tree is an unbiased sampler of the filter, so filter path collisions estimate $\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_w$ without bias.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: expectations of the sampled matrices → Bochner integrals, with integrability of the integrands stated in the conclusion; reason: so that Lean's default value 0 for non-integrable functions cannot satisfy the statement; the sampled entries are bounded
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 6.4, p.22

import Mathlib
import Definitions.Def_WalkTreeCluster_Laws
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 6.4** (Unbiased estimation of the filter), p.22 (PDF p.25). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

For every stage `i ≥ 0` and vertex `u`: (1) `E X_{u,i} = F_i 1_u`; (2)
`E X^{keep}_{u,i} = (1 − δ)⁻¹ F_i D_{i+1} 1_u`, entrywise, with every entry integrable.

**Formalization Note.** Expectations are entrywise Bochner integrals under the laws of Algorithms
1–5; integrability of every entry is part of the conclusion, so that a default value `0` cannot
satisfy the identity. The parameter range is `d ≥ 1`, an undirected graph without parallel edges,
`0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴` (Table 1). -/
theorem lemma_6_4 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (i : ℕ) (u : Fin n) :
    (∀ (σ : FPath i) (z : Fin n),
      Integrable (fun X : Mat n i => X σ z) (walkLaw nbr ϵ ϕ i u) ∧
      ∫ X, X σ z ∂(walkLaw nbr ϵ ϕ i u) = filter nbr ϵ ϕ i (coord u) σ z) ∧
    (∀ (σ : FPath i) (z : Fin n),
      Integrable (fun X : Mat n i => X σ z) (keepWalkLaw nbr ϵ ϕ i u) ∧
      ∫ X, X σ z ∂(keepWalkLaw nbr ϵ ϕ i u) =
        (1 / (1 - deltaParam ϵ ϕ)) *
          filter nbr ϵ ϕ i ((Ddiag nbr ϵ ϕ (i + 1)).mulVec (coord u)) σ z) := by sorry

end WalkTreeCluster
