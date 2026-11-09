-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_8_3
-- name    : WalkTreeCluster.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:57:02.727015+00:00
-- url     : https://prove2.me/theorems/800e95b5-cef3-4b92-ac9b-f59f62c1aa4e
-- title:
--   Lemma 8.3: local variation $\le2c_{\rm loc}a^{66}|C|$ and the collision-moment profile, with an absolute $c_{\rm loc}$
-- statement:
--   There is an absolute constant $c_{\rm loc}>0$ such that, for every undirected $d$-regular graph ($d\ge1$), every $0<\phi\le1$ and $\epsilon>0$ with $a\le10^{-4}$, every family of clusters and every cluster $C$:
--   1. (Local variation)
--   $$\sum_{i\ge1}\alpha^{2i}\sum_{u\in C}\|F_i(\mathbb 1_u-u_C)\|_{F,w}^4\le2c_{\rm loc}a^{66}|C| ;$$
--   2. (Collision-moment profile) for every $u\in V$ there is a sequence $e_i(u)\ge0$, $i\ge1$, with
--   $$\alpha^{2i}\big\|\mathbb E[X_{u,i}^{\otimes2}]\big\|_{F,w}^2\le128\frac{\alpha^i}{|C|}+e_i(u)\quad(i\ge1,\ \alpha^i\le|C|),\qquad\sum_{i\ge1}\sum_{u\in C}e_i(u)\le c_{\rm loc}a^{62}|C| .$$
--   The constant does not depend on $V\setminus C$.
--
--   Table 1 defines $c_0$ from $c_{\rm loc}$.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - generalization: the parameters of Table 1, including 0 < ϵ ≤ c₀ϕ² → only 0 < ϕ ≤ 1, ϵ > 0 and a = (8ϵ/ϕ²)^{1/1000} ≤ 10⁻⁴ (the Table 1 bound on a); reason: ϵ ≤ c₀ϕ² implies a ≤ 10⁻⁴ because c₀ ≤ 10⁻⁴⁰⁰⁰/8, so the Lean statement specializes to the page's; the result is used for Lemma 8.3, whose constant c_loc defines c₀, so it cannot depend on c₀
--   - encoding: infinite sums of nonnegative terms → sums in [0, ∞] (ENNReal); reason: the sums are of nonnegative terms; no default value can occur
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 8.3, p.48

import Mathlib
import Definitions.Def_WalkTreeCluster_LocalVariationConst

namespace WalkTreeCluster

/-- **Lemma 8.3** (Local variation and the moments used to choose keep factors), p.48 (PDF p.51).
Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…).

There is an absolute constant `c_loc > 0` such that, for every cluster `C`,
(1) `Σ_{i ≥ 1} α^{2i} Σ_{u ∈ C} ‖F_i(1_u − u_C)‖⁴_{F,w} ≤ 2 c_loc a^{66} |C|`, and
(2) for every `u ∈ V` there is a sequence `e_i(u) ≥ 0` with
`α^{2i} ‖E[X_{u,i}^{⊗2}]‖²_{F,w} ≤ 128 α^i/|C| + e_i(u)` (`i ≥ 1`, `α^i ≤ |C|`) and
`Σ_{i ≥ 1} Σ_{u ∈ C} e_i(u) ≤ c_loc a^{62} |C|`.
The constant does not depend on `V ∖ C`.

**Formalization Note.** `LocalVariationConst c_loc` is the conclusion with the constant `c_loc`,
quantified over every graph and cluster family in the parameter range (`d ≥ 1`, undirected, no
parallel edges, `0 < ϕ ≤ 1`, `ϵ > 0`, `a ≤ 10⁻⁴`); so `c_loc` is chosen before the graph. -/
theorem lemma_8_3 : ∃ cloc : ℝ, LocalVariationConst cloc := by sorry

end WalkTreeCluster
