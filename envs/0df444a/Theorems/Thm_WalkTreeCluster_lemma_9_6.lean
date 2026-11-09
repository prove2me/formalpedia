-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_9_6
-- name    : WalkTreeCluster.lemma_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:02:39.813437+00:00
-- url     : https://prove2.me/theorems/7ef2e806-9694-4185-b768-6e391f184b85
-- title:
--   Lemma 9.6: $|B_{\rm noise}|\le5000a|S|$ and $|B|\le Ca|S|$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$) and $\mathcal C$ a family of clusters for $\epsilon,\phi$, with the parameters of Table 1, $0<\epsilon\le c_0\phi^2$ and $c_0$ defined from the constant $c_{\rm loc}$ of Lemma 8.3.
--   For the sets of Definition 9.5,
--   $$|B_{\rm noise}|\le5000\,a\,|S|,\qquad|B|\le C\,a\,|S|,$$
--   where $C$ is an absolute constant.
--
--   Together with Lemma 8.1 this bounds the exceptional set of Theorem 1.3.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - reading: c_loc is the absolute constant of Lemma 8.3 and c₀ = (1/8)min{10⁻⁴, (128c_loc)^{−1/60}}^{1000} (Table 1) → any c_loc for which the conclusion of Lemma 8.3 holds (LocalVariationConst c_loc), with ϵ ≤ c0Param(c_loc)·ϕ²; reason: Table 1 defines c₀ from the constant of Lemma 8.3; with lemma_8_3 (∃ c_loc) this is the page's statement
--   - reading: the unnamed constant C in |B| ≤ Ca|S| → ∃ C, chosen after c_loc and before the graph; reason: the proof gives C = 5000 + 2c_loc, an absolute constant (p.66)
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 9.6 with Definition 9.5, p.65

import Mathlib
import Definitions.Def_WalkTreeCluster_ExceptionalSets
import Definitions.Def_WalkTreeCluster_LocalVariationConst

namespace WalkTreeCluster

/-- **Lemma 9.6** (The number of exceptional noise vertices), p.65 (PDF p.68), with Definition 9.5.
Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…).

The sets of Definition 9.5 satisfy `|B_noise| ≤ 5000a|S|` and `|B| ≤ Ca|S|`.

**Formalization Note.** `C` is a constant chosen before the graph and the parameters (the proof
gives `5000 + 2c_loc`). `c_loc` is a constant for which the conclusion of Lemma 8.3 holds, and the
parameters satisfy Table 1 with `c₀ = c0Param c_loc`: `d ≥ 1`, undirected, no parallel edges,
`0 < ϕ ≤ 1`, `0 < ϵ ≤ c₀ϕ²`. -/
theorem lemma_9_6 (cloc : ℝ) (hcloc : LocalVariationConst cloc) :
    ∃ C : ℝ, ∀ (n d : ℕ) (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
      (𝒞 : Finset (Finset (Fin n))),
      1 ≤ d → IsUndirected nbr → NoParallel nbr → 0 < ϕ → ϕ ≤ 1 → 0 < ϵ →
      ϵ ≤ c0Param cloc * ϕ ^ 2 → IsClusterFamily nbr ϵ ϕ 𝒞 →
      ((Bnoise nbr ϵ ϕ 𝒞).card : ℝ) ≤ 5000 * aParam ϵ ϕ * (clusterUnion 𝒞).card ∧
      ((Bexc nbr ϵ ϕ 𝒞).card : ℝ) ≤ C * aParam ϵ ϕ * (clusterUnion 𝒞).card := by sorry

end WalkTreeCluster
