-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_9_7
-- name    : WalkTreeCluster.lemma_9_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:02:21.890494+00:00
-- url     : https://prove2.me/theorems/d3e00d4e-e037-4abb-b650-b7bdca07036a
-- title:
--   Lemma 9.7: with accurate estimates, a trial decides $u,v\notin B$ correctly and reaches a decision by stage $h_*$
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$) and $\mathcal C$ a family of clusters for $\epsilon,\phi$, with the parameters of Table 1, $0<\epsilon\le c_0\phi^2$ and $c_0$ defined from the constant $c_{\rm loc}$ of Lemma 8.3.
--   Let $u\ne v$ be vertices outside $B$ (Definition 9.5) with $\{u,v\}\cap S\ne\emptyset$, and set
--   $$k=\min\{|C(z)|:z\in\{u,v\}\cap S\},\qquad h_*=\min\{h\ge1:\alpha^h\ge a^{10}k/\alpha\}.$$
--   Fix one depth-$h$ trial of Cluster$(u,v)$ (Algorithm 7) whose returned values satisfy
--   $$\big|\langle F_i\mathbb 1_z,F_i\mathbb 1_{z'}\rangle_{w,h}-\langle F_i\mathbb 1_z,F_i\mathbb 1_{z'}\rangle_w\big|\le\frac{a^{20}}{\alpha^i}\qquad(z,z'\in\{u,v\},\ 1\le i\le h).$$
--   1. Whenever the trial tests the closeness of $u$ and $v$ (line 14), $A_r=\textit{same}$ if and only if some cluster contains both $u$ and $v$.
--   2. If $h\ge h_*$ and the trial does not exceed its work cap, it tests the closeness of $u$ and $v$ at a stage $j\le h_*$.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - reading: c_loc is the absolute constant of Lemma 8.3 and c₀ = (1/8)min{10⁻⁴, (128c_loc)^{−1/60}}^{1000} (Table 1) → any c_loc for which the conclusion of Lemma 8.3 holds (LocalVariationConst c_loc), with ϵ ≤ c0Param(c_loc)·ϕ²; reason: Table 1 defines c₀ from the constant of Lemma 8.3; with lemma_8_3 (∃ c_loc) this is the page's statement
--   - encoding: one depth-h trial of Cluster(u, v) that does not exceed its work cap → the uncapped trial function trialOutcome / testStage of its estimates; reason: lines 8–18 of Algorithm 7 are a deterministic function of the returned values
--   - encoding: the values returned by the calls of one trial, each satisfying the accuracy bound → estimates at every stage 1 ≤ i ≤ h for all five calls, each within a²⁰/αⁱ; reason: the trial function never reads the other values, so imposing the bound on them as well changes nothing
--   - encoding: h* = min{…} → any h* that is the least element of the set (IsLeast); reason: the set is nonempty since α > 1; same instances
--   - encoding: k = min{|C(z)| : z ∈ {u, v} ∩ S} → any k that is the least size of a cluster containing u or v (IsLeast); reason: C(z) is the cluster containing z; same value
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 9.7, p.67

import Mathlib
import Definitions.Def_WalkTreeCluster_ExceptionalSets
import Definitions.Def_WalkTreeCluster_LocalVariationConst
import Definitions.Def_WalkTreeCluster_TrialDecision

namespace WalkTreeCluster

/-- **Lemma 9.7** (Pair classification with one clustered endpoint), p.67 (PDF p.70).
Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…).

Let distinct `u, v ∈ V ∖ B` satisfy `{u, v} ∩ S ≠ ∅`, and set
`k = min{|C(z)| : z ∈ {u, v} ∩ S}`, `h_* = min{h ≥ 1 : α^h ≥ a^{10} k/α}`. Fix one depth-`h` trial of
`Cluster(u, v)` whose returned values satisfy (129):
`|⟨F_i1_z, F_i1_{z'}⟩_{w,h} − ⟨F_i1_z, F_i1_{z'}⟩_w| ≤ a^{20}/α^i` (`z, z' ∈ {u, v}`, `1 ≤ i ≤ h`).
(1) Whenever Cluster tests the closeness of `u` and `v` (line 14),
`A_r = same ⟺ ∃ C ∈ 𝒞 : {u, v} ⊆ C`.
(2) If `h ≥ h_*` and the trial does not exceed the work cap, Cluster tests the closeness of `u`
and `v` at a stage `j ≤ h_*`.

**Formalization Note.** The trial is the uncapped trial function `trialOutcome`; (129) is imposed
on every estimate at every stage `1 ≤ i ≤ h`. `B` is Definition 9.5's `B_clusters ∪ B_noise`. `k`
is the least size of a cluster containing `u` or `v`, and `h_*` is given by `IsLeast`. `c_loc` is
a constant for which the conclusion of Lemma 8.3 holds, and the parameters satisfy Table 1 with
`c₀ = c0Param c_loc`. -/
theorem lemma_9_7 (cloc : ℝ) (hcloc : LocalVariationConst cloc) {n d : ℕ}
    (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d) (hU : IsUndirected nbr)
    (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (hϵc : ϵ ≤ c0Param cloc * ϕ ^ 2) (𝒞 : Finset (Finset (Fin n)))
    (h𝒞 : IsClusterFamily nbr ϵ ϕ 𝒞) (u v : Fin n) (huv : u ≠ v)
    (huB : u ∉ Bexc nbr ϵ ϕ 𝒞) (hvB : v ∉ Bexc nbr ϵ ϕ 𝒞)
    (hS : u ∈ clusterUnion 𝒞 ∨ v ∈ clusterUnion 𝒞) (k : ℕ)
    (hk : IsLeast {m : ℕ | ∃ C ∈ 𝒞, (u ∈ C ∨ v ∈ C) ∧ m = C.card} k) (hstar : ℕ)
    (hhstar : IsLeast {h : ℕ | 1 ≤ h ∧
      aParam ϵ ϕ ^ 10 * (k : ℝ) / alphaParam ϵ ϕ ≤ alphaParam ϵ ϕ ^ h} hstar)
    (h : ℕ) (normEst : ℕ → Bool → ℝ) (uuEst vvEst uvEst : ℕ → ℝ)
    (hacc : ∀ i : ℕ, 1 ≤ i → i ≤ h →
      |normEst i false - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u))
          (filter nbr ϵ ϕ i (coord u))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |normEst i true - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord v))
          (filter nbr ϵ ϕ i (coord v))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |uuEst i - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u))
          (filter nbr ϵ ϕ i (coord u))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |vvEst i - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord v))
          (filter nbr ϵ ϕ i (coord v))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |uvEst i - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u))
          (filter nbr ϵ ϕ i (coord v))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i) :
    (∀ (j : ℕ) (b : Bool), trialOutcome ϵ ϕ h normEst uuEst vvEst uvEst = some (j, b) →
      (b = true ↔ ∃ C ∈ 𝒞, u ∈ C ∧ v ∈ C)) ∧
    (hstar ≤ h → ∃ j ≤ hstar, testStage ϵ ϕ h normEst = some j) := by sorry

end WalkTreeCluster
