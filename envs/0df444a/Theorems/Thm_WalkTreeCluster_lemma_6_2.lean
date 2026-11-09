-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_6_2
-- name    : WalkTreeCluster.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:26.330045+00:00
-- url     : https://prove2.me/theorems/500bdb51-4830-4a22-b072-3b747f8bb584
-- title:
--   Lemma 6.2: $\|\mathbb E[X_i^{\otimes2}]\|_{F,w}^2\le64\alpha^{2-2i}$, the fourth-moment bound, and $\|\mathbb E[(X_i^{\rm keep})^{\otimes2}]\|_{F,w}\le\alpha^{-i}$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$), $0<\phi\le1$, $\epsilon>0$, with the parameters of Table 1 and $a\le10^{-4}$.
--   For every vertex $u$ and stage $i\ge0$, with $X_i=X_{u,i}$ and $X_i^{\rm keep}=X^{\rm keep}_{u,i}$:
--   1. $\big\|\mathbb E[X_i^{\otimes2}]\big\|_{F,w}^2\le64\alpha^{2-2i}$;
--   2. $\big\|\mathbb E[X_i^{\otimes4}]\big\|_{F,w}^2\le1200\Big(\alpha^{-2i}\big\|\mathbb E[X_i^{\otimes2}]\big\|_{F,w}^2+\big\|\mathbb E[X_i^{\otimes2}]\big\|_{F,w}^4\Big)$;
--   3. $\big\|\mathbb E[(X_i^{\rm keep})^{\otimes2}]\big\|_{F,w}\le\alpha^{-i}$.
--
--   These moment bounds control the variance of filter path collisions and of the Keep statistic.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: expectations of the sampled matrices → Bochner integrals, with integrability of the integrands stated in the conclusion; reason: so that Lean's default value 0 for non-integrable functions cannot satisfy the statement; the sampled entries are bounded
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 6.2, p.21

import Mathlib
import Definitions.Def_WalkTreeCluster_Laws
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 6.2** (Moments of filter path walks), p.21 (PDF p.24). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

For every stage `i ≥ 0` and vertex `u`, with `X_i = X_{u,i}`:
(1) `‖E[X_i^{⊗2}]‖²_{F,w} ≤ 64 α^{2−2i}`;
(2) `‖E[X_i^{⊗4}]‖²_{F,w} ≤ 1200 (α^{−2i} ‖E[X_i^{⊗2}]‖²_{F,w} + ‖E[X_i^{⊗2}]‖⁴_{F,w})`;
(3) `‖E[(X^{keep}_i)^{⊗2}]‖_{F,w} ≤ α^{−i}`.

**Formalization Note.** The moments are Bochner integrals; integrability of every product of two and
of four entries of `X_{u,i}`, and of two entries of `X^{keep}_{u,i}`, is part of the conclusion.
`‖E[X^{⊗2}]‖⁴_{F,w}` is the square of `secondMomentNormSq`; (3) is the norm, the square root of
`secondMomentNormSq`. Powers of `α` with integer exponents are `zpow`. Parameter range: `d ≥ 1`,
undirected, no parallel edges, `0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem lemma_6_2 {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d)
    (hU : IsUndirected nbr) (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (ha : aParam ϵ ϕ ≤ 1 / 10 ^ 4) (i : ℕ) (u : Fin n) :
    MomentIntegrable 2 (walkLaw nbr ϵ ϕ i u) ∧ MomentIntegrable 4 (walkLaw nbr ϵ ϕ i u) ∧
    MomentIntegrable 2 (keepWalkLaw nbr ϵ ϕ i u) ∧
    secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u) ≤
      64 * alphaParam ϵ ϕ ^ ((2 : ℤ) - 2 * (i : ℤ)) ∧
    fourthMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u) ≤
      1200 * (alphaParam ϵ ϕ ^ (-(2 * (i : ℤ))) *
          secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u) +
        secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u) ^ 2) ∧
    Real.sqrt (secondMomentNormSq (aParam ϵ ϕ) (keepWalkLaw nbr ϵ ϕ i u)) ≤
      alphaParam ϵ ϕ ^ (-(i : ℤ)) := by sorry

end WalkTreeCluster
