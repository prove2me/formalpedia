-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_7_2
-- name    : WalkTreeCluster.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:56:45.254559+00:00
-- url     : https://prove2.me/theorems/da124251-e9c2-4fd7-beaa-3ec74000ef72
-- title:
--   Lemma 7.2: $0\le\|f\|_2^2-\|F_iD_i^{1/2}f\|_{F,w}^2\le E_i(f)\le\frac5a\|\sqrt{I-K_i^2}f\|_2^2$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   Put $K_i=D_i^{1/2}M^tD_i^{1/2}$. For every stage $i\ge0$ and $f\in\mathbb R^V$ let
--   $$E_i(f)=\Big(\|f\|_2^2-\sum_\sigma\|(F_iD_i^{1/2}f)_\sigma\|_2^2\Big)+\sum_{\sigma:\theta(\sigma)>0}\|(F_iD_i^{1/2}f)_\sigma\|_2^2,$$
--   both sums over $\sigma\in\{L,H\}^i$ (Eq. (52)). Then
--   $$0\le\|f\|_2^2-\|F_iD_i^{1/2}f\|_{F,w}^2\le E_i(f)\le\frac5a\big\|\sqrt{I-K_i^2}\,f\big\|_2^2 .$$
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: ‖√(I − K_i²) f‖²₂ → the quadratic form fᵀ(I − K_i²)f; reason: equal for the symmetric K_i with 0 ⪯ K_i ⪯ I; no matrix square root needed
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 7.2, p.38

import Mathlib
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 7.2** (Preservation by the full filter), p.38 (PDF p.41). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

Put `K_i = D_i^{1/2} M^t D_i^{1/2}`. For every stage `i ≥ 0` and `f ∈ ℝ^V` define (Eq. (52))
`E_i(f) = (‖f‖²₂ − Σ_σ ‖(F_i D_i^{1/2} f)_σ‖²₂) + Σ_{σ : θ(σ) > 0} ‖(F_i D_i^{1/2} f)_σ‖²₂`, both sums over
`σ ∈ {L, H}^i`. Then
`0 ≤ ‖f‖²₂ − ‖F_i D_i^{1/2} f‖²_{F,w} ≤ E_i(f) ≤ (5/a) ‖√(I − K_i²) f‖²₂`.

**Formalization Note.** `‖√(I − K_i²) f‖²₂` is written as the quadratic form `fᵀ(I − K_i²)f`, which
equals it for the symmetric `K_i` with `0 ⪯ K_i ⪯ I` and needs no matrix square root. Parameter
range: `d ≥ 1`, undirected, no parallel edges, `0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem lemma_7_2 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (i : ℕ) (f : Fin n → ℝ) :
    let G := filter nbr ϵ ϕ i ((Dsqrt nbr ϵ ϕ i).mulVec f)
    let E := (∑ z, f z ^ 2 - frobSq G) +
      ∑ σ ∈ Finset.univ.filter (fun σ : FPath i => 0 < theta (aParam ϵ ϕ) σ), ∑ z, G σ z ^ 2
    0 ≤ ∑ z, f z ^ 2 - wNormSq (aParam ϵ ϕ) G ∧
    ∑ z, f z ^ 2 - wNormSq (aParam ϵ ϕ) G ≤ E ∧
    E ≤ (5 / aParam ϵ ϕ) *
      (f ⬝ᵥ ((1 - Kmat nbr ϵ ϕ i ^ 2).mulVec f)) := by sorry

end WalkTreeCluster
