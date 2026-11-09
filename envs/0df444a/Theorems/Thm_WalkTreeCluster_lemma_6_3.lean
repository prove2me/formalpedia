-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_6_3
-- name    : WalkTreeCluster.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:31.19296+00:00
-- url     : https://prove2.me/theorems/39114770-c8a6-46cd-af3b-71c6bac4f43c
-- title:
--   Lemma 6.3: $\mathbb E[\tau(i)^4]\le12(\mathbb E[\tau(i)^2])^2$ and $1-\mathbb E[\tau(i)]\asymp\min\{1,\alpha^{2i}\|\mathbb E[X_i^{\otimes2}]\|_{F,w}^2\}$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   Fix a vertex $u$ and a stage $i\ge1$, let $(X_{i,r},X'_{i,r})$, $r=1,\dots,B$, be independent copies of $(X_{u,i},X'_{u,i})$, and let
--   $$\tau(i)=\Big(1+\frac{64\alpha^{2i}}{B}\sum_{r=1}^B\langle X_{i,r},X'_{i,r}\rangle_w^2\Big)^{-1/4}.$$
--   Then
--   1. $\mathbb E[\tau(i)^4]\le12\big(\mathbb E[\tau(i)^2]\big)^2$;
--   2. $\displaystyle\frac1{9604}\min\big\{1,\alpha^{2i}\|\mathbb E[X_i^{\otimes2}]\|_{F,w}^2\big\}\le1-\mathbb E[\tau(i)]\le16\alpha^{2i}\|\mathbb E[X_i^{\otimes2}]\|_{F,w}^2$, and
--   $$1-\mathbb E[\tau(i)]\le1-\mathbb E[\tau(i)^2]\le2\big(1-\mathbb E[\tau(i)]\big)\le32\alpha^{2i}\|\mathbb E[X_i^{\otimes2}]\|_{F,w}^2 .$$
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: expectations of the sampled matrices → Bochner integrals, with integrability of the integrands stated in the conclusion; reason: so that Lean's default value 0 for non-integrable functions cannot satisfy the statement; the sampled entries are bounded
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 6.3, p.21

import Mathlib
import Definitions.Def_WalkTreeCluster_Laws
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 6.3** (Bounds for the fractional keep factor), p.21 (PDF p.24). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

Fix a stage `i ≥ 1` and a vertex `u`, and let `(X_{i,r}, X'_{i,r})`, `r = 1, …, B`, be independent
copies of `(X_{u,i}, X'_{u,i})`. The factor
`τ(i) = (1 + 64α^{2i} B⁻¹ Σ_r ⟨X_{i,r}, X'_{i,r}⟩²_w)^{−1/4}` of Algorithm 5, line 5, satisfies
(1) `E[τ(i)⁴] ≤ 12 (E[τ(i)²])²`;
(2) `(1/9604) min{1, α^{2i} ‖E[X_i^{⊗2}]‖²_{F,w}} ≤ 1 − E[τ(i)] ≤ 16 α^{2i} ‖E[X_i^{⊗2}]‖²_{F,w}`, and
`1 − E[τ(i)] ≤ 1 − E[τ(i)²] ≤ 2(1 − E[τ(i)]) ≤ 32 α^{2i} ‖E[X_i^{⊗2}]‖²_{F,w}`.

**Formalization Note.** `E[τ(i)^k]` is the integral of `tauStat^k` under the joint law
`tauSampleLaw` of the `2B` samples; integrability of `τ(i)` is part of the conclusion (it takes
values in `(0, 1]`). Parameter range: `d ≥ 1`, undirected, no parallel edges, `0 < ϕ ≤ 1`,
`ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem lemma_6_3 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (i : ℕ) (hi : 1 ≤ i) (u : Fin n) :
    Integrable (tauStat ϵ ϕ i) (tauSampleLaw nbr ϵ ϕ i u) ∧
    ∫ S, tauStat ϵ ϕ i S ^ 4 ∂(tauSampleLaw nbr ϵ ϕ i u) ≤
      12 * (∫ S, tauStat ϵ ϕ i S ^ 2 ∂(tauSampleLaw nbr ϵ ϕ i u)) ^ 2 ∧
    (1 / 9604) * min 1 (alphaParam ϵ ϕ ^ (2 * i) *
        secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u)) ≤
      1 - ∫ S, tauStat ϵ ϕ i S ∂(tauSampleLaw nbr ϵ ϕ i u) ∧
    1 - ∫ S, tauStat ϵ ϕ i S ∂(tauSampleLaw nbr ϵ ϕ i u) ≤
      16 * alphaParam ϵ ϕ ^ (2 * i) * secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u) ∧
    1 - ∫ S, tauStat ϵ ϕ i S ∂(tauSampleLaw nbr ϵ ϕ i u) ≤
      1 - ∫ S, tauStat ϵ ϕ i S ^ 2 ∂(tauSampleLaw nbr ϵ ϕ i u) ∧
    1 - ∫ S, tauStat ϵ ϕ i S ^ 2 ∂(tauSampleLaw nbr ϵ ϕ i u) ≤
      2 * (1 - ∫ S, tauStat ϵ ϕ i S ∂(tauSampleLaw nbr ϵ ϕ i u)) ∧
    2 * (1 - ∫ S, tauStat ϵ ϕ i S ∂(tauSampleLaw nbr ϵ ϕ i u)) ≤
      32 * alphaParam ϵ ϕ ^ (2 * i) *
        secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u) := by sorry

end WalkTreeCluster
