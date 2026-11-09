-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_6_5
-- name    : WalkTreeCluster.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:53:38.029218+00:00
-- url     : https://prove2.me/theorems/3175ddcd-9d8f-4331-9cb7-f1879cdce14d
-- title:
--   Lemma 6.5: $\sum_{i\ge0}\alpha^{2i}\|\mathbb E[X_i^{\otimes2}]\|_{F,w}^2\le Ca^{-10}$ and the three companion sums
-- statement:
--   There is an absolute constant $C$ such that, for every undirected $d$-regular graph ($d\ge1$), every $0<\phi\le1$ and $\epsilon>0$ with $a\le10^{-4}$, and every vertex $u$:
--   1. $\displaystyle\sum_{i\ge0}\alpha^{2i}\big\|\mathbb E[X_i^{\otimes2}]\big\|_{F,w}^2\le Ca^{-10}$ and $\displaystyle\sum_{i\ge0}\alpha^{2i}\big\|\mathbb E[(X_i^{\rm keep})^{\otimes2}]\big\|_{F,w}^2\le Ca^{-6}$;
--   2. $\displaystyle\sum_{i\ge0}\alpha^{2i}\|F_i\mathbb 1_u\|_{F,w}^4\le Ca^{-10}$ and $\displaystyle\sum_{i\ge0}\alpha^{2i}\|F_iD_{i+1}\mathbb 1_u\|_{F,w}^4\le Ca^{-6}$.
--
--   These bounds control the cumulative loss of Keep scores over all stages.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: series of nonnegative terms; an absolute constant C → sums in [0, ∞] (ENNReal); ∃ C before the graph and the parameters; reason: no default value can occur; 'absolute' places C first
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 6.5, p.23

import Mathlib
import Definitions.Def_WalkTreeCluster_Laws
import Definitions.Def_WalkTreeCluster_Filter

open MeasureTheory

namespace WalkTreeCluster

/-- **Lemma 6.5** (Pointwise sums over all stages), p.23 (PDF p.26). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

There is an absolute constant `C` such that, for every vertex `u`,
(1) `Σ_{i ≥ 0} α^{2i} ‖E[X_i^{⊗2}]‖²_{F,w} ≤ C a^{−10}` and
`Σ_{i ≥ 0} α^{2i} ‖E[(X^{keep}_i)^{⊗2}]‖²_{F,w} ≤ C a^{−6}`;
(2) `Σ_{i ≥ 0} α^{2i} ‖F_i 1_u‖⁴_{F,w} ≤ C a^{−10}` and `Σ_{i ≥ 0} α^{2i} ‖F_i D_{i+1} 1_u‖⁴_{F,w} ≤ C a^{−6}`.

**Formalization Note.** `C` is chosen before the graph and the parameters. The four series have
nonnegative terms and are summed in `ℝ≥0∞`. Parameter range: `d ≥ 1`, undirected, no parallel
edges, `0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`. -/
theorem lemma_6_5 :
    ∃ C : ℝ, ∀ (n d : ℕ) (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ),
      1 ≤ d → IsUndirected nbr → NoParallel nbr → 0 < ϕ → ϕ ≤ 1 → 0 < ϵ →
      aParam ϵ ϕ ≤ 1 / 10 ^ 4 → ∀ u : Fin n,
      (∑' i : ℕ, ENNReal.ofReal (alphaParam ϵ ϕ ^ (2 * i) *
          secondMomentNormSq (aParam ϵ ϕ) (walkLaw nbr ϵ ϕ i u))) ≤
        ENNReal.ofReal (C * aParam ϵ ϕ ^ (-10 : ℤ)) ∧
      (∑' i : ℕ, ENNReal.ofReal (alphaParam ϵ ϕ ^ (2 * i) *
          secondMomentNormSq (aParam ϵ ϕ) (keepWalkLaw nbr ϵ ϕ i u))) ≤
        ENNReal.ofReal (C * aParam ϵ ϕ ^ (-6 : ℤ)) ∧
      (∑' i : ℕ, ENNReal.ofReal (alphaParam ϵ ϕ ^ (2 * i) *
          wNormSq (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u)) ^ 2)) ≤
        ENNReal.ofReal (C * aParam ϵ ϕ ^ (-10 : ℤ)) ∧
      (∑' i : ℕ, ENNReal.ofReal (alphaParam ϵ ϕ ^ (2 * i) *
          wNormSq (aParam ϵ ϕ)
            (filter nbr ϵ ϕ i ((Ddiag nbr ϵ ϕ (i + 1)).mulVec (coord u))) ^ 2)) ≤
        ENNReal.ofReal (C * aParam ϵ ϕ ^ (-6 : ℤ)) := by sorry

end WalkTreeCluster
