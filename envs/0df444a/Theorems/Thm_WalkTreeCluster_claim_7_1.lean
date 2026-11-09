-- Prove2me | Theorems.Thm_WalkTreeCluster_claim_7_1
-- name    : WalkTreeCluster.claim_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:54:26.872346+00:00
-- url     : https://prove2.me/theorems/b1b41257-94e7-4dfd-9268-dd559dda4250
-- title:
--   Claim 7.1: $\|F_iD_i^{1/2}\|_{\rm op},\|F_iD_{i+1}\|_{\rm op}\le1$ and $\|F_if\|_{F,w}^2\le(1+9a^{40})\|f\|_2^2$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   For every stage $i\ge0$:
--   1. $\|F_iD_i^{1/2}\|_{\rm op}\le1$ and $\|F_iD_{i+1}\|_{\rm op}\le1$;
--   2. $\|F_if\|_{F,w}^2\le(1+9a^{40})\|f\|_2^2$ for all $f\in\mathbb R^V$;
--   3. for $i\ge1$, $\|F_if\|_{F,w}^2\le\|D_i^{1/2}M^tf\|_2^2+9a^{40}\|f\|_2^2$.
--   In (1) the input carries the Euclidean norm and the output the unweighted Frobenius norm $\sum_\sigma\|(\cdot)_\sigma\|_2^2$.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: ‖T‖_op ≤ 1 → ‖Tf‖² ≤ ‖f‖² for every f (unweighted Frobenius norm on the output); reason: definition of the operator norm
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Claim 7.1, p.36

import Mathlib
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Claim 7.1** (Contraction bounds), p.36 (PDF p.39). Kapralov–Kochetkova, *Sublinear Time
Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission (manuscript sha256
638eeef1…).

For every stage `i ≥ 0`:
(1) `‖F_i D_i^{1/2}‖_op ≤ 1` and `‖F_i D_{i+1}‖_op ≤ 1`;
(2) `‖F_i f‖²_{F,w} ≤ (1 + 9a^{40}) ‖f‖²₂` for every `f ∈ ℝ^V`;
(3) for `i ≥ 1`, `‖F_i f‖²_{F,w} ≤ ‖D_i^{1/2} M^t f‖²₂ + 9a^{40} ‖f‖²₂`.

**Formalization Note.** In (1) the operator norm is Euclidean on the input and the unweighted
Frobenius norm `Σ_σ ‖(·)_σ‖²₂` on the output (`frobSq`); `‖T‖_op ≤ 1` is stated as
`‖T f‖² ≤ ‖f‖²` for every `f`. Parameter range: `d ≥ 1`, undirected, no parallel edges,
`0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem claim_7_1 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (i : ℕ) (f : Fin n → ℝ) :
    frobSq (filter nbr ϵ ϕ i ((Dsqrt nbr ϵ ϕ i).mulVec f)) ≤ ∑ z, f z ^ 2 ∧
    frobSq (filter nbr ϵ ϕ i ((Ddiag nbr ϵ ϕ (i + 1)).mulVec f)) ≤ ∑ z, f z ^ 2 ∧
    wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i f) ≤ (1 + 9 * aParam ϵ ϕ ^ 40) * ∑ z, f z ^ 2 ∧
    (1 ≤ i → wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i f) ≤
      ∑ z, ((Dsqrt nbr ϵ ϕ i * (walkMatrix nbr) ^ tParam ϵ ϕ).mulVec f z) ^ 2 +
        9 * aParam ϵ ϕ ^ 40 * ∑ z, f z ^ 2) := by sorry

end WalkTreeCluster
